//! Interface to manipulate UNIX files on an ext2 filesystem.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::mem::size_of;
use core::ops::{AddAssign, SubAssign};
use core::ptr::addr_of;
use core::slice::from_raw_parts;

use itertools::Itertools;

use super::directory::Entry;
use super::error::Ext2Error;
use super::inode::Inode;
use super::{Celled, Ext2};
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::file::{self, DirectoryEntry, Stat};
use crate::fs::error::FsError;
use crate::fs::ext2::block::Block;
use crate::fs::PATH_MAX;
use crate::io::{Read, Seek, SeekFrom, Write};
use crate::types::{Blkcnt, Blksize, Dev, Gid, Ino, Mode, Nlink, Off, Time, Timespec, Uid};

/// Limit in bytes for the length of a pointed path of a symbolic link to be store in an inode and not in a separate data block.
pub const SYMBOLIC_LINK_INODE_STORE_LIMIT: usize = 60;

/// General file implementation.
pub struct File<D: Device<u8, Ext2Error>> {
    /// Ext2 object associated with the device containing this file.
    filesystem: Celled<Ext2<D>>,

    /// Inode number of the inode corresponding to the file.
    inode_number: u32,

    /// Inode corresponding to the file.
    inode: Inode,

    /// Read/Write offset in bytes (can be manipulated with [`Seek`]).
    io_offset: u64,
}

impl<D: Device<u8, Ext2Error>> Debug for File<D> {
    #[inline]
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("File")
            .field("device_id", &self.filesystem.borrow().device_id)
            .field("inode_number", &self.inode_number)
            .field("inode", &self.inode)
            .field("io_offset", &self.io_offset)
            .finish()
    }
}

impl<D: Device<u8, Ext2Error>> File<D> {
    /// Returns a new ext2's [`File`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::parse`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let fs = filesystem.borrow();
        let inode = Inode::parse(&fs.device, &fs.superblock, inode_number)?;
        Ok(Self {
            filesystem: filesystem.clone(),
            inode_number,
            inode,
            io_offset: 0,
        })
    }

    /// Updates the inner [`Inode`].
    fn update_inner_inode(&mut self) -> Result<(), Error<Ext2Error>> {
        let fs = self.filesystem.borrow();
        self.inode = Inode::parse(&fs.device, &fs.superblock, self.inode_number)?;
        Ok(())
    }

    ///  Sets the file's inode to the given object.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device cannot be written.
    ///
    /// # Safety
    ///
    /// Must ensure that the given inode is coherent with the current state of the filesystem.
    unsafe fn set_inode(&mut self, inode: &Inode) -> Result<(), Error<Ext2Error>> {
        let fs = self.filesystem.borrow();
        let celled_device = fs.device.clone();

        let starting_addr = Inode::starting_addr(&celled_device, fs.superblock(), self.inode_number)?;

        let mut device = fs.device.borrow_mut();
        device.write_at(starting_addr, *inode)?;

        drop(device);
        drop(fs);

        self.update_inner_inode()?;

        Ok(())
    }
}

impl<D: Device<u8, Ext2Error>> file::File for File<D> {
    #[inline]
    fn stat(&self) -> file::Stat {
        let filesystem = self.filesystem.borrow();

        Stat {
            dev: Dev(filesystem.device_id),
            ino: Ino(self.inode_number),
            mode: Mode(self.inode.mode),
            nlink: Nlink(u32::from(self.inode.links_count)),
            uid: Uid(self.inode.uid),
            gid: Gid(self.inode.gid),
            rdev: Dev::default(),
            size: Off(self.inode.data_size().try_into().unwrap_or_default()),
            atim: Timespec {
                tv_sec: Time(self.inode.atime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            mtim: Timespec {
                tv_sec: Time(self.inode.mtime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            ctim: Timespec {
                tv_sec: Time(self.inode.ctime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            blksize: Blksize(filesystem.superblock.block_size().try_into().unwrap_or_default()),
            blkcnt: Blkcnt(self.inode.blocks.try_into().unwrap_or_default()),
        }
    }
}

/// Implementation of a regular file.
#[derive(Debug)]
pub struct Regular<D: Device<u8, Ext2Error>> {
    /// Inner file containing the regular file.
    file: File<D>,
}

impl<D: Device<u8, Ext2Error>> Read for File<D> {
    type Error = Ext2Error;

    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<Self::Error>> {
        let filesystem = self.filesystem.borrow();
        self.inode
            .read_data(&filesystem.device, &filesystem.superblock, buf, self.io_offset)
            .map(|bytes| {
                self.io_offset += bytes as u64;
                bytes
            })
    }
}

/// State of a block during the writing process.
///
/// Used to keep track of modifications during writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    /// This block is already present on the device and should be updated only if it was previously not full and if data is
    /// Updated at its end.
    Unmodified,

    /// This block has been updated so it should be written on the device.
    Updated,
}

/// Block with a block state.
#[derive(Debug, Clone, Copy)]
struct BlockWithState {
    /// Represents a block number.
    block: u32,

    /// State of this block.
    state: State,
}

impl<D: Device<u8, Ext2Error>> Write for File<D> {
    type Error = Ext2Error;

    #[inline]
    #[allow(clippy::too_many_lines)]
    #[allow(clippy::cognitive_complexity)] // TODO: make this understandable for a human
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<Self::Error>> {
        /// Writes the given `blocks` number in the indirect block with the number `block_number`.
        fn write_indirect_block<D: Device<u8, Ext2Error>>(
            filesystem: &Celled<Ext2<D>>,
            block_number: u32,
            blocks: &Vec<u32>,
        ) -> Result<(), Error<Ext2Error>> {
            let mut indirect_block = Block::new(filesystem.clone(), block_number);
            // SAFETY: it is always possible to cast a `u32` to four `u8`
            let buffer = unsafe { from_raw_parts::<u8>(blocks.as_ptr().cast(), blocks.len() * size_of::<u32>() / size_of::<u8>()) };
            indirect_block.write(buffer).map(|_| ())
        }

        /// Write a data block given with its state, starting the buffer `buf` at the given offset `offset`.
        fn write_data_block<D: Device<u8, Ext2Error>>(
            filesystem: &Celled<Ext2<D>>,
            block_number: u32,
            buf: &[u8],
            offset: &mut u64,
            written_bytes: &mut usize,
        ) -> Result<(), Error<Ext2Error>> {
            let fs = filesystem.borrow();
            let block_size = u64::from(fs.superblock().block_size());

            // SAFETY: `block_size` is lower than `usize::MAX` when `usize` is at least `u16`
            let block_size_usize = unsafe { usize::try_from(fs.superblock().block_size()).unwrap_unchecked() };

            if *offset >= block_size {
                offset.sub_assign(block_size);
            } else if *offset > 0 {
                let mut block = Block::new(filesystem.clone(), block_number);

                block.seek(SeekFrom::Start(*offset))?;

                // SAFETY: `offset < block_size` which is lower than `usize::MAX` when `usize` is at least `u16`
                let bytes_to_end_block = block_size_usize - unsafe { usize::try_from(*offset).unwrap_unchecked() };
                let length = bytes_to_end_block.min(buf.len() - *written_bytes);

                // SAFETY: the block has been Updated so `written_bytes < `bytes_to_write`
                block.write(unsafe { buf.get_unchecked(*written_bytes..*written_bytes + length) })?;

                *offset = 0_u64;
                written_bytes.add_assign(length);
            } else {
                let length = block_size_usize.min(buf.len() - *written_bytes);

                let mut block = Block::new(filesystem.clone(), block_number);

                // SAFETY: the block has been Updated so `written_bytes < `bytes_to_write`
                block.write(unsafe { buf.get_unchecked(*written_bytes..*written_bytes + length) })?;

                written_bytes.add_assign(length);
            }

            Ok(())
        }

        let fs = self.filesystem.borrow_mut();
        let block_size = u64::from(fs.superblock().block_size());

        if buf.len() as u64 > fs.superblock().max_file_size() {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::OutOfBounds(buf.len() as i128))));
        }

        // Calcul of the number of needed data blocks
        let bytes_to_write = buf.len() as u64;
        let blocks_needed =
            (bytes_to_write + self.io_offset) / block_size + u64::from((bytes_to_write + self.io_offset) % block_size != 0);
        let (
            initial_direct_block_pointers,
            (initial_singly_indirect_block_pointer, initial_singly_indirect_blocks),
            (initial_doubly_indirect_block_pointer, initial_doubly_indirect_blocks),
            (initial_triply_indirect_block_pointer, initial_triply_indirect_blocks),
        ) = self.inode.data_blocks(&fs.device, fs.superblock())?;
        let current_data_block_number = (initial_direct_block_pointers.len()
            + initial_singly_indirect_blocks.len()
            + initial_doubly_indirect_blocks.len()
            + initial_triply_indirect_blocks.len()) as u64;
        let data_blocks_to_request = blocks_needed.saturating_sub(current_data_block_number);

        drop(fs);

        let mut singly_indirect_block_pointer = BlockWithState {
            block: initial_singly_indirect_block_pointer,
            state: State::Unmodified,
        };
        let mut doubly_indirect_block_pointer = BlockWithState {
            block: initial_doubly_indirect_block_pointer,
            state: State::Unmodified,
        };
        let mut triply_indirect_block_pointer = BlockWithState {
            block: initial_triply_indirect_block_pointer,
            state: State::Unmodified,
        };

        let mut direct_block_pointers = initial_direct_block_pointers;
        let mut singly_indirect_blocks = initial_singly_indirect_blocks;
        let mut doubly_indirect_blocks = initial_doubly_indirect_blocks
            .into_iter()
            .map(|(block_pointer, blocks)| {
                (
                    BlockWithState {
                        block: block_pointer,
                        state: State::Unmodified,
                    },
                    blocks,
                )
            })
            .collect_vec();
        let mut triply_indirect_blocks = initial_triply_indirect_blocks
            .into_iter()
            .map(|(block_pointer_pointer, block_pointers)| {
                (
                    BlockWithState {
                        block: block_pointer_pointer,
                        state: State::Unmodified,
                    },
                    block_pointers
                        .into_iter()
                        .map(|(block_pointer, blocks)| {
                            (
                                BlockWithState {
                                    block: block_pointer,
                                    state: State::Unmodified,
                                },
                                blocks,
                            )
                        })
                        .collect_vec(),
                )
            })
            .collect_vec();

        // Computation of the number of needed indirection blocks
        let max_data_blocks_per_simple_indirection =
            // SAFETY: size_of::<u32>() == 4
            block_size / unsafe { u64::try_from(size_of::<u32>()).unwrap_unchecked() };
        let max_data_blocks_per_double_indirection =
            max_data_blocks_per_simple_indirection * max_data_blocks_per_simple_indirection;

        let mut total_blocks_to_request = data_blocks_to_request;
        let mut remaining_data_blocks = data_blocks_to_request;
        remaining_data_blocks = remaining_data_blocks.saturating_sub(12 - direct_block_pointers.len() as u64);

        let mut total_simply_indirect_blocks = 0_usize;
        let mut total_doubly_indirect_blocks = 0_usize;
        let mut total_triply_indirect_blocks = 0_usize;

        // Simple indirection
        if remaining_data_blocks > 0 {
            if singly_indirect_blocks.is_empty() {
                total_blocks_to_request += 1;
            }

            let simply_indirect_block_number = (max_data_blocks_per_simple_indirection
                // SAFETY: an indirection block contains at most few thousands of block numbers
                - unsafe { u64::try_from(singly_indirect_blocks.len()).unwrap_unchecked() })
            .min(remaining_data_blocks);
            // SAFETY: `remaining_data_blocks < u32::MAX`
            total_simply_indirect_blocks = unsafe { usize::try_from(simply_indirect_block_number).unwrap_unchecked() };
            remaining_data_blocks -= simply_indirect_block_number;
        }

        // Double indirection
        if remaining_data_blocks > 0 {
            doubly_indirect_blocks.last().map_or_else(
                || {
                    total_blocks_to_request += 1;
                },
                |simple_indirect_block| {
                    remaining_data_blocks -= remaining_data_blocks
                        .min(max_data_blocks_per_simple_indirection)
                        .saturating_sub(simple_indirect_block.1.len() as u64);
                },
            );

            // The max number of data blocks per simple indirection is equal to the number of simple indirection blocks per double
            // indirection, and so on.

            // SAFETY: `max_data_blocks_per_simple_indirection << u32::MAX`
            total_doubly_indirect_blocks = unsafe {
                usize::try_from(
                    ((remaining_data_blocks / max_data_blocks_per_simple_indirection)
                        + u64::from(remaining_data_blocks % max_data_blocks_per_simple_indirection != 0))
                    .min(max_data_blocks_per_simple_indirection),
                )
                .unwrap_unchecked()
            };
            let singly_indirect_blocks_to_request = ((remaining_data_blocks / max_data_blocks_per_simple_indirection)
                + u64::from(remaining_data_blocks % max_data_blocks_per_simple_indirection != 0))
            .min(max_data_blocks_per_simple_indirection)
            .saturating_sub(doubly_indirect_blocks.len() as u64);

            total_blocks_to_request += singly_indirect_blocks_to_request;
            remaining_data_blocks =
                remaining_data_blocks.saturating_sub(max_data_blocks_per_simple_indirection * singly_indirect_blocks_to_request);
        }

        // Triple indirection
        if remaining_data_blocks > 0 {
            match triply_indirect_blocks.last() {
                None => total_blocks_to_request += 1,
                Some(doubly_indirect_block) => {
                    doubly_indirect_block.1.last().map_or_else(
                        || total_blocks_to_request += 1,
                        |simple_indirect_block| {
                            remaining_data_blocks -= remaining_data_blocks
                                .min(max_data_blocks_per_simple_indirection)
                                .saturating_sub(simple_indirect_block.1.len() as u64);
                        },
                    );

                    let singly_indirect_blocks_to_request = ((remaining_data_blocks / max_data_blocks_per_simple_indirection)
                        + u64::from(remaining_data_blocks % max_data_blocks_per_simple_indirection != 0))
                    .min(max_data_blocks_per_simple_indirection)
                    .saturating_sub(doubly_indirect_blocks.len() as u64);

                    total_blocks_to_request += singly_indirect_blocks_to_request;
                    remaining_data_blocks = remaining_data_blocks
                        .saturating_sub(max_data_blocks_per_simple_indirection * singly_indirect_blocks_to_request);
                },
            }

            total_triply_indirect_blocks =
                // SAFETY: `max_data_blocks_per_simple_indirection << u32::MAX`
                unsafe { usize::try_from((remaining_data_blocks / max_data_blocks_per_double_indirection) + u64::from(remaining_data_blocks % max_data_blocks_per_double_indirection != 0)).unwrap_unchecked() };
            let full_doubly_indirect_blocks_to_request = (remaining_data_blocks / max_data_blocks_per_double_indirection)
                .saturating_sub(triply_indirect_blocks.len() as u64);

            total_blocks_to_request += full_doubly_indirect_blocks_to_request * max_data_blocks_per_simple_indirection;
            remaining_data_blocks -= full_doubly_indirect_blocks_to_request * max_data_blocks_per_double_indirection;

            // `remaining_data_blocks` modulo `max_data_blocks_per_double_indirection` didn't change in the last assignment
            if remaining_data_blocks % max_data_blocks_per_double_indirection != 0 {
                total_blocks_to_request += 1;

                let singly_indirect_blocks_to_request = remaining_data_blocks / max_data_blocks_per_simple_indirection
                    + u64::from(remaining_data_blocks % max_data_blocks_per_simple_indirection != 0);
                total_blocks_to_request += singly_indirect_blocks_to_request;

                #[allow(unused_assignments)] // Useful to keep for debugging, `remaining_data_blocks` should be equal to `0`.
                remaining_data_blocks = remaining_data_blocks
                    .saturating_sub(max_data_blocks_per_simple_indirection * singly_indirect_blocks_to_request);
            }
        }

        // Add the free blocks where it's necessary.
        let free_block_numbers = &mut self
            .filesystem
            // SAFETY: `blocks_to_request <= blocks_needed < u32::MAX`
            .free_blocks(unsafe { u32::try_from(total_blocks_to_request).unwrap_unchecked() })?
            .into_iter();

        let mut free_block_copied = free_block_numbers.clone();

        // Direct block pointers
        direct_block_pointers.append(&mut free_block_numbers.take(12 - direct_block_pointers.len()).collect_vec());

        // Singly indirected block pointer
        if singly_indirect_block_pointer.block == 0 && let Some(block) = free_block_numbers.next() {
            singly_indirect_block_pointer.block = block;
            singly_indirect_block_pointer.state = State::Updated;
        }

        if total_simply_indirect_blocks - singly_indirect_blocks.len() > 0 {
            singly_indirect_block_pointer.state = State::Updated;
            singly_indirect_blocks.append(
                &mut free_block_numbers
                    .take(total_simply_indirect_blocks - singly_indirect_blocks.len())
                    .collect_vec(),
            );
        }

        // Doubly indirected block pointer
        if doubly_indirect_block_pointer.block == 0 && let Some(block) = free_block_numbers.next() {
            doubly_indirect_block_pointer.block = block;
            doubly_indirect_block_pointer.state = State::Updated;
        }

        if let Some(block_with_state) = doubly_indirect_blocks.last_mut() {
            let blocks_added =
                // SAFETY: `free_block_numbers.len() << u32::MAX`
                unsafe { usize::try_from(max_data_blocks_per_simple_indirection).unwrap_unchecked() } - block_with_state.1.len();
            if blocks_added > 0 {
                block_with_state.0.state = State::Updated;
                block_with_state.1.append(&mut free_block_numbers.take(blocks_added).collect_vec());
            }
        }

        while doubly_indirect_blocks.len() < total_doubly_indirect_blocks {
            // SAFETY: `free_block_numbers` contains the exact amount of needed free blocks
            let indirect_block = unsafe { free_block_numbers.next().unwrap_unchecked() };
            doubly_indirect_blocks.push((
                BlockWithState {
                    block: indirect_block,
                    state: State::Updated,
                },
                free_block_numbers
                    // SAFETY: `max_data_blocks_per_simple_indirection` is lower than `usize::MAX` when `usize` is at least
                    // `u16`
                    .take(unsafe { usize::try_from(max_data_blocks_per_simple_indirection).unwrap_unchecked() })
                    .collect_vec(),
            ));
        }

        // Triply indirected block pointer
        if triply_indirect_block_pointer.block == 0 && let Some(block) = free_block_numbers.next() {
            triply_indirect_block_pointer.block = block;
            triply_indirect_block_pointer.state = State::Updated;
        }

        if let Some(doubly_indirect_block_with_state) = triply_indirect_blocks.last_mut() {
            if let Some(simply_indirect_block) = doubly_indirect_block_with_state.1.last_mut() {
                // SAFETY: `free_block_numbers.len() << u32::MAX`
                let new_blocks = unsafe { usize::try_from(max_data_blocks_per_simple_indirection).unwrap_unchecked() }
                    - simply_indirect_block.1.len();

                if new_blocks > 0 {
                    doubly_indirect_block_with_state.0.state = State::Updated;
                    simply_indirect_block.1.append(&mut free_block_numbers.take(new_blocks).collect_vec());
                }
            }

            while (doubly_indirect_block_with_state.1.len() as u64) < max_data_blocks_per_simple_indirection
                && !free_block_numbers.is_empty()
            {
                // SAFETY: `free_block_numbers` contains the exact amount of needed free blocks
                let indirect_block = unsafe { free_block_numbers.next().unwrap_unchecked() };
                doubly_indirect_blocks.push((
                    BlockWithState {
                        block: indirect_block,
                        state: State::Updated,
                    },
                    free_block_numbers
                        // SAFETY: `max_data_blocks_per_simple_indirection` is lower than `usize::MAX` when `usize` is at least
                        // `u16`
                        .take(unsafe { usize::try_from(max_data_blocks_per_simple_indirection).unwrap_unchecked() })
                        .collect_vec(),
                ));
            }
        }

        while triply_indirect_blocks.len() < total_triply_indirect_blocks {
            // SAFETY: `free_block_numbers` contains the exact amount of needed free blocks
            let triply_indirect_block = unsafe { free_block_numbers.next().unwrap_unchecked() };
            let mut doubly_indirect_blocks = Vec::new();

            while (doubly_indirect_blocks.len() as u64) < max_data_blocks_per_simple_indirection && !free_block_numbers.is_empty() {
                // SAFETY: `free_block_numbers` contains the exact amount of needed free blocks
                let doubly_indirect_block = unsafe { free_block_numbers.next().unwrap_unchecked() };

                doubly_indirect_blocks.push((
                    BlockWithState {
                        block: doubly_indirect_block,
                        state: State::Updated,
                    },
                    free_block_numbers
                        // SAFETY: `max_data_blocks_per_simple_indirection` is lower than `usize::MAX` when `usize` is at least
                        // `u16`
                        .take(unsafe { usize::try_from(max_data_blocks_per_simple_indirection).unwrap_unchecked() })
                        .collect_vec(),
                ));
            }

            triply_indirect_blocks.push((
                BlockWithState {
                    block: triply_indirect_block,
                    state: State::Updated,
                },
                doubly_indirect_blocks,
            ));
        }

        // Write everything that has to change.

        let mut offset = self.io_offset;
        let mut written_bytes = 0_usize;

        // Direct block pointers
        for block in &direct_block_pointers {
            write_data_block(&self.filesystem, *block, buf, &mut offset, &mut written_bytes)?;
        }

        // Singly indirected block pointer
        if singly_indirect_block_pointer.state == State::Updated {
            write_indirect_block(&self.filesystem, singly_indirect_block_pointer.block, &singly_indirect_blocks)?;
        }

        for block in singly_indirect_blocks {
            write_data_block(&self.filesystem, block, buf, &mut offset, &mut written_bytes)?;
        }

        // Doubly indirected block pointer
        if doubly_indirect_block_pointer.state == State::Updated {
            write_indirect_block(
                &self.filesystem,
                doubly_indirect_block_pointer.block,
                &doubly_indirect_blocks
                    .iter()
                    .map(|block_pointer_with_state| block_pointer_with_state.0.block)
                    .collect_vec(),
            )?;
        }

        for block_pointer in doubly_indirect_blocks {
            if block_pointer.0.state == State::Updated {
                write_indirect_block(&self.filesystem, block_pointer.0.block, &block_pointer.1)?;
            }

            for block in block_pointer.1 {
                write_data_block(&self.filesystem, block, buf, &mut offset, &mut written_bytes)?;
            }
        }

        // Triply indirected block pointer
        if triply_indirect_block_pointer.state == State::Updated {
            write_indirect_block(
                &self.filesystem,
                triply_indirect_block_pointer.block,
                &triply_indirect_blocks
                    .iter()
                    .map(|block_with_state| block_with_state.0.block)
                    .collect_vec(),
            )?;
        }

        for block_pointer_pointer in triply_indirect_blocks {
            if block_pointer_pointer.0.state == State::Updated {
                write_indirect_block(
                    &self.filesystem,
                    block_pointer_pointer.0.block,
                    &block_pointer_pointer.1.iter().map(|block_pointer| block_pointer.0.block).collect_vec(),
                )?;
            }

            for block_pointer in block_pointer_pointer.1 {
                if block_pointer.0.state == State::Updated {
                    write_indirect_block(&self.filesystem, block_pointer.0.block, &block_pointer.1)?;
                }

                for block in block_pointer.1 {
                    write_data_block(&self.filesystem, block, buf, &mut offset, &mut written_bytes)?;
                }
            }
        }

        let mut updated_inode = self.inode;

        let mut direct_block_pointers = direct_block_pointers.clone();
        direct_block_pointers.append(&mut vec![0_u32; 12].into_iter().take(12 - direct_block_pointers.len()).collect_vec());
        let mut updated_direct_block_pointers = updated_inode.direct_block_pointers;
        updated_direct_block_pointers.clone_from_slice(&direct_block_pointers);
        updated_inode.direct_block_pointers = updated_direct_block_pointers;

        updated_inode.singly_indirect_block_pointer = singly_indirect_block_pointer.block;
        updated_inode.doubly_indirect_block_pointer = doubly_indirect_block_pointer.block;
        updated_inode.triply_indirect_block_pointer = triply_indirect_block_pointer.block;

        let new_size = self.inode.data_size().max(self.io_offset + buf.len() as u64);

        // SAFETY: the result cannot be greater than `u32::MAX`
        updated_inode.size = unsafe { u32::try_from(new_size & u64::from(u32::MAX)).unwrap_unchecked() };
        // TODO: update `updated_inode.blocks`

        assert!(u32::try_from(new_size).is_ok(), "Search how to deal with bigger files");

        // SAFETY: the updated inode contains the right inode created in this function
        unsafe { self.set_inode(&updated_inode) }?;

        // TODO: be smarter to avoid make 1000000 calls to device's `write`
        free_block_copied.try_for_each(|block| Block::new(self.filesystem.clone(), block).set_used())?;

        Ok(written_bytes)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Error<Ext2Error>> {
        Ok(())
    }
}

impl<D: Device<u8, Ext2Error>> Seek for File<D> {
    type Error = Ext2Error;

    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<Ext2Error>> {
        // SAFETY: it is safe to assume that the file length is smaller than 2^63 bytes long
        let file_length = unsafe { i64::try_from(self.inode.data_size()).unwrap_unchecked() };

        let previous_offset = self.io_offset;
        match pos {
            SeekFrom::Start(offset) => self.io_offset = offset,
            SeekFrom::End(back_offset) => {
                self.io_offset = TryInto::<u64>::try_into(file_length - back_offset)
                    .map_err(|_err| Ext2Error::OutOfBounds(i128::from(file_length - back_offset)))?;
            },
            SeekFrom::Current(add_offset) => {
                // SAFETY: it is safe to assume that the file has a length smaller than 2^64 bytes.
                self.io_offset = (unsafe { TryInto::<i64>::try_into(previous_offset).unwrap_unchecked() } + add_offset)
                    .try_into()
                    .map_err(|_err| {
                        Ext2Error::OutOfBounds(i128::from(
                            // SAFETY: it is safe to assume that the file has a length smaller than 2^64 bytes.
                            unsafe { TryInto::<i64>::try_into(previous_offset).unwrap_unchecked() } + add_offset,
                        ))
                    })?;
            },
        };

        if self.io_offset >= self.inode.data_size() {
            Err(Error::Fs(FsError::Implementation(Ext2Error::OutOfBounds(self.io_offset.into()))))
        } else {
            Ok(previous_offset)
        }
    }
}

impl<D: Device<u8, Ext2Error>> Regular<D> {
    /// Returns a new ext2's [`Regular`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Ext2::inode`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        Ok(Self {
            file: File::new(&filesystem.clone(), inode_number)?,
        })
    }

    /// Reads all the content of the file and returns it in a byte vector.
    ///
    /// Does not move the offset for I/O operations used by [`Seek`].
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::read_data`].
    ///
    /// # Panics
    ///
    /// This function panics if the total size of the device cannot be loaded in RAM.
    #[inline]
    pub fn read_all(&mut self) -> Result<Vec<u8>, Error<Ext2Error>> {
        let mut buffer = vec![
            0_u8;
            self.file
                .inode
                .data_size()
                .try_into()
                .expect("The size of the file's content is greater than the size representable on this computer.")
        ];
        let previous_offset = self.seek(SeekFrom::Start(0))?;
        self.read(&mut buffer)?;
        self.seek(SeekFrom::Start(previous_offset))?;
        Ok(buffer)
    }
}

impl<D: Device<u8, Ext2Error>> file::File for Regular<D> {
    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }
}

impl<D: Device<u8, Ext2Error>> Read for Regular<D> {
    type Error = Ext2Error;

    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<Ext2Error>> {
        self.file.read(buf)
    }
}

impl<D: Device<u8, Ext2Error>> Write for Regular<D> {
    type Error = Ext2Error;

    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<Ext2Error>> {
        self.file.write(buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Error<Ext2Error>> {
        self.file.flush()
    }
}

impl<D: Device<u8, Ext2Error>> Seek for Regular<D> {
    type Error = Ext2Error;

    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<Ext2Error>> {
        self.file.seek(pos)
    }
}

impl<D: Device<u8, Ext2Error>> file::Regular for Regular<D> {}

/// Interface for ext2's directories.
#[derive(Debug)]
pub struct Directory<D: Device<u8, Ext2Error>> {
    /// Inner file containing the regular file.
    file: File<D>,

    /// Entries contained in this directory.
    entries: Vec<Entry>,
}

impl<D: Device<u8, Ext2Error>> Directory<D> {
    /// Returns the directory located at the given inode number.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Entry::parse`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let file = File::new(filesystem, inode_number)?;
        let fs = filesystem.borrow();

        let mut entries = Vec::new();

        let mut accumulated_size = 0_u32;
        while accumulated_size < fs.superblock().block_size() {
            let starting_addr =
                Address::from((file.inode.direct_block_pointers[0] * fs.superblock().block_size() + accumulated_size) as usize);
            // SAFETY: `starting_addr` contains the beginning of an entry
            let entry = unsafe { Entry::parse(&fs.device, starting_addr) }?;
            accumulated_size += u32::from(entry.rec_len);
            entries.push(entry);
        }

        Ok(Self { file, entries })
    }
}

impl<D: Device<u8, Ext2Error>> file::File for Directory<D> {
    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }
}

impl<Dev: Device<u8, Ext2Error>> file::Directory for Directory<Dev> {
    type Error = Ext2Error;
    type File = File<Dev>;
    type Regular = Regular<Dev>;
    type SymbolicLink = SymbolicLink<Dev>;

    #[inline]
    fn entries(&self) -> Result<Vec<file::DirectoryEntry<Self>>, Error<Ext2Error>> {
        let mut entries = Vec::new();

        for entry in &self.entries {
            entries.push(DirectoryEntry {
                // SAFETY: it is checked at the entry creation that the name is a valid CString
                filename: unsafe { entry.name.clone().try_into().unwrap_unchecked() },
                file: self.file.filesystem.file(entry.inode)?,
            });
        }

        Ok(entries)
    }
}

/// Interface for ext2's symbolic links.
#[derive(Debug)]
pub struct SymbolicLink<D: Device<u8, Ext2Error>> {
    /// Inner file containing the symbolic link.
    file: File<D>,

    /// Read/Write offset (can be manipulated with [`Seek`]).
    pointed_file: String,
}

impl<D: Device<u8, Ext2Error>> SymbolicLink<D> {
    /// Returns a new ext2's [`Regular`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns a [`BadString`](Ext2Error::BadString) if the content of the given inode does not look like a valid path.
    ///
    /// Returns a [`NameTooLong`](crate::fs::error::FsError::NameTooLong) if the size of the inode's content is greater than
    /// [`PATH_MAX`].
    ///
    /// Otherwise, returns the same errors as [`Ext2::inode`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let fs = filesystem.borrow();
        let file = File::new(&filesystem.clone(), inode_number)?;

        let data_size = usize::try_from(file.inode.data_size()).unwrap_or(PATH_MAX);

        let mut buffer = vec![0_u8; data_size];

        if data_size < SYMBOLIC_LINK_INODE_STORE_LIMIT {
            // SAFETY: it is always possible to read a slice of u8
            buffer.clone_from_slice(unsafe {
                core::slice::from_raw_parts(addr_of!(file.inode.direct_block_pointers).cast(), data_size)
            });
        } else {
            let _: usize = file.inode.read_data(&fs.device, fs.superblock(), &mut buffer, 0)?;
        }
        let pointed_file = buffer.split(|char| *char == b'\0').next().ok_or(Ext2Error::BadString)?.to_vec();
        Ok(Self {
            file,
            pointed_file: String::from_utf8(pointed_file).map_err(|_err| Ext2Error::BadString)?,
        })
    }
}

impl<D: Device<u8, Ext2Error>> file::File for SymbolicLink<D> {
    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }
}

impl<D: Device<u8, Ext2Error>> file::SymbolicLink for SymbolicLink<D> {
    #[inline]
    fn pointed_file(&self) -> &str {
        &self.pointed_file
    }
}

#[cfg(test)]
mod test {
    use alloc::string::{String, ToString};
    use alloc::vec;
    use alloc::vec::Vec;
    use core::cell::RefCell;
    use std::fs::{self, File};

    use itertools::Itertools;

    use crate::dev::sector::Address;
    use crate::file::TypeWithFile;
    use crate::fs::ext2::directory::Entry;
    use crate::fs::ext2::file::Directory;
    use crate::fs::ext2::inode::{Inode, ROOT_DIRECTORY_INODE};
    use crate::fs::ext2::superblock::Superblock;
    use crate::fs::ext2::{Celled, Ext2};
    use crate::io::{Seek, SeekFrom, Write};
    use crate::path::UnixStr;

    #[test]
    fn parse_root() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();
        assert_eq!(
            root.entries
                .into_iter()
                .map(|entry| entry.name.to_string_lossy().to_string())
                .collect::<Vec<String>>(),
            vec![".", "..", "lost+found", "big_file", "symlink"]
        );
    }

    #[test]
    fn parse_root_entries() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        let root_inode = Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).unwrap();

        let dot = unsafe {
            Entry::parse(&celled_file, Address::new((root_inode.direct_block_pointers[0] * superblock.block_size()) as usize))
        }
        .unwrap();
        let two_dots = unsafe {
            Entry::parse(
                &celled_file,
                Address::new((root_inode.direct_block_pointers[0] * superblock.block_size()) as usize + dot.rec_len as usize),
            )
        }
        .unwrap();
        let lost_and_found = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len) as usize,
                ),
            )
        }
        .unwrap();
        let big_file = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len + lost_and_found.rec_len) as usize,
                ),
            )
        }
        .unwrap();
        let symlink = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len + lost_and_found.rec_len + big_file.rec_len) as usize,
                ),
            )
        }
        .unwrap();

        assert_eq!(dot.name.as_c_str().to_string_lossy(), ".");
        assert_eq!(two_dots.name.as_c_str().to_string_lossy(), "..");
        assert_eq!(lost_and_found.name.as_c_str().to_string_lossy(), "lost+found");
        assert_eq!(big_file.name.as_c_str().to_string_lossy(), "big_file");
        assert_eq!(symlink.name.as_c_str().to_string_lossy(), "symlink");
    }

    #[test]
    fn parse_big_file_inode_data() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();

        let fs = ext2.borrow();
        let big_file_inode_number = root
            .entries
            .iter()
            .find(|entry| entry.name.to_string_lossy() == "big_file")
            .unwrap()
            .inode;
        let big_file_inode = fs.inode(big_file_inode_number).unwrap();

        let singly_indirect_block_pointer = big_file_inode.singly_indirect_block_pointer;
        let doubly_indirect_block_pointer = big_file_inode.doubly_indirect_block_pointer;
        assert_ne!(singly_indirect_block_pointer, 0);
        assert_ne!(doubly_indirect_block_pointer, 0);

        assert_ne!(big_file_inode.data_size(), 0);

        for offset in 0_usize..1_024_usize {
            let mut buffer = [0_u8; 1_024];
            big_file_inode
                .read_data(&fs.device, fs.superblock(), &mut buffer, (offset * 1_024) as u64)
                .unwrap();

            assert_eq!(buffer.iter().all_equal_value(), Ok(&1));
        }

        let mut buffer = [0_u8; 1_024];
        big_file_inode.read_data(&fs.device, fs.superblock(), &mut buffer, 0x0010_0000).unwrap();
        assert_eq!(buffer.iter().all_equal_value(), Ok(&0));
    }

    #[test]
    fn read_file() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/io_operations.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());

        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        assert_eq!(foo.read_all().unwrap(), b"Hello world!\n");
    }

    #[test]
    fn read_symlink() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();

        let TypeWithFile::SymbolicLink(symlink) =
            crate::file::Directory::entry(&root, UnixStr::new("symlink").unwrap()).unwrap().unwrap()
        else {
            panic!("`symlink` has been created as a symbolic link")
        };

        assert_eq!(symlink.pointed_file, "big_file");
    }

    #[test]
    fn set_inode() {
        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_set_inode.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_set_inode.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut new_inode = foo.file.inode;
        new_inode.uid = 0x1234;
        new_inode.gid = 0x2345;
        new_inode.flags = 0xabcd;
        unsafe { foo.file.set_inode(&new_inode) }.unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());
        assert_eq!(foo.file.inode, new_inode);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_set_inode.ext2").unwrap();
    }

    #[test]
    fn write_file_dbp_replace_without_allocation() {
        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_dbp_replace_without_allocation.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_dbp_replace_without_allocation.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        foo.seek(SeekFrom::Start(6)).unwrap();
        let replace_text = b"earth";
        foo.write(replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(String::from_utf8(foo.read_all().unwrap()).unwrap(), "Hello earth!\n");

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_dbp_replace_without_allocation.ext2").unwrap();
    }

    #[test]
    fn write_file_dbp_extend_without_allocation() {
        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_without_allocation.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_without_allocation.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        foo.seek(SeekFrom::Start(6)).unwrap();
        let replace_text = b"earth!\nI love dogs!\n";
        foo.write(replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(foo.read_all().unwrap(), b"Hello earth!\nI love dogs!\n");

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_without_allocation.ext2").unwrap();
    }

    #[test]
    fn write_file_dbp_extend_with_allocation() {
        const BYTES_TO_WRITE: usize = 12_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_with_allocation.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_with_allocation.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let replace_text = &[b'a'; BYTES_TO_WRITE];
        foo.write(replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap().into_iter().all_equal_value(), Ok(b'a'));

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_with_allocation.ext2").unwrap();
    }

    #[test]
    fn write_file_singly_indirect_block_pointer() {
        const BYTES_TO_WRITE: usize = 23_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_singly_indirect_block_pointer.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_singly_indirect_block_pointer.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut replace_text = vec![b'a'; BYTES_TO_WRITE / 2];
        replace_text.append(&mut vec![b'b'; BYTES_TO_WRITE / 2]);
        foo.write(&replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap(), replace_text);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_singly_indirect_block_pointer.ext2").unwrap();
    }

    #[test]
    fn write_file_doubly_indirect_block_pointer() {
        const BYTES_TO_WRITE: usize = 400_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_doubly_indirect_block_pointer.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_doubly_indirect_block_pointer.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut replace_text = vec![b'a'; BYTES_TO_WRITE / 2];
        replace_text.append(&mut vec![b'b'; BYTES_TO_WRITE / 2]);
        foo.write(&replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap(), replace_text);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_doubly_indirect_block_pointer.ext2").unwrap();
    }

    #[test]
    fn write_file_triply_indirect_block_pointer() {
        const BYTES_TO_WRITE: usize = 70_000_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_triply_indirect_block_pointer.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_triply_indirect_block_pointer.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut replace_text = vec![b'a'; BYTES_TO_WRITE / 2];
        replace_text.append(&mut vec![b'b'; BYTES_TO_WRITE / 2]);
        foo.write(&replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap(), replace_text);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_triply_indirect_block_pointer.ext2").unwrap();
    }
}
