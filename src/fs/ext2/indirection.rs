//! Manipulation of indirection in ext2, for the major part for inodes' blocks.
//!
//! See [this Wikipedia section](https://en.wikipedia.org/wiki/Ext2#Inodes) for more information.

use alloc::vec::Vec;

use itertools::Itertools;

/// Block indirections.
///
/// See [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#i-block) for more information.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Indirection {
    /// Directly accessible blocks.
    Direct,

    /// Simply indirected blocks.
    Simple,

    /// Doubly indirected blocks.
    Double,

    /// Triply indirected blocks.
    Triple,
}

/// Type alias representing direct blocks.
pub type DirectBlocks = Vec<u32>;

/// Type alias representing a single indirection block.
#[allow(clippy::module_name_repetitions)]
pub type SimpleIndirection = (u32, Vec<u32>);

/// Type alias representing a double indirection block.
#[allow(clippy::module_name_repetitions)]
pub type DoubleIndirection = (u32, Vec<SimpleIndirection>);

/// Type alias representing a triple indirection block.
#[allow(clippy::module_name_repetitions)]
pub type TripleIndirection = (u32, Vec<DoubleIndirection>);

/// Represents a structure that contains indirections.
trait Indirected {
    /// Fetches the block at given `offset` knowing the number of blocks in each group.
    fn resolve_indirection(&self, offset: u32, blocks_per_indirection: u32) -> Option<u32>;
}

impl Indirected for DirectBlocks {
    #[inline]
    fn resolve_indirection(&self, offset: u32, _blocks_per_indirection: u32) -> Option<u32> {
        self.get(offset as usize).copied()
    }
}

impl Indirected for SimpleIndirection {
    #[inline]
    fn resolve_indirection(&self, offset: u32, _blocks_per_indirection: u32) -> Option<u32> {
        self.1.get(offset as usize).copied()
    }
}

impl Indirected for DoubleIndirection {
    #[inline]
    fn resolve_indirection(&self, offset: u32, blocks_per_indirection: u32) -> Option<u32> {
        let double_indirection_index = offset / blocks_per_indirection;
        let simple_indirection_index = offset % blocks_per_indirection;
        self.1.get(double_indirection_index as usize).and_then(|simple_indirection_block| {
            simple_indirection_block
                .1
                .resolve_indirection(simple_indirection_index, blocks_per_indirection)
        })
    }
}

impl Indirected for TripleIndirection {
    #[inline]
    fn resolve_indirection(&self, offset: u32, blocks_per_indirection: u32) -> Option<u32> {
        let triple_indirection_index = offset / (blocks_per_indirection * blocks_per_indirection);
        let double_indirection_index = offset % (blocks_per_indirection * blocks_per_indirection);
        self.1.get(triple_indirection_index as usize).and_then(|double_indirection_block| {
            double_indirection_block.resolve_indirection(double_indirection_index, blocks_per_indirection)
        })
    }
}

/// Type for data blocks in an inode.
///
/// Only contains the real data blocks (with a number different than 0).
///
/// The parameter `DBPC` is the maximal number of direct block pointers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndirectedBlocks<const DBPC: u32> {
    /// Number of blocks contained in each indirection.
    ///
    /// In ext2 filesystems, this always should be equal to `superblock.block_size() / 4`.
    blocks_per_indirection: u32,

    /// The direct block numbers.
    direct_blocks: DirectBlocks,

    /// The singly indirected block numbers.
    singly_indirected_blocks: SimpleIndirection,

    /// The doubly indirected block numbers.
    doubly_indirected_blocks: DoubleIndirection,

    /// The triply indirected block numbers.
    triply_indirected_blocks: TripleIndirection,
}

impl<const DBPC: u32> IndirectedBlocks<DBPC> {
    /// Creates a new instance from complete list of data blocks.
    #[inline]
    #[must_use]
    pub(crate) fn new(
        blocks_per_indirection: u32,
        direct_blocks: DirectBlocks,
        singly_indirected_blocks: SimpleIndirection,
        doubly_indirected_blocks: DoubleIndirection,
        triply_indirected_blocks: TripleIndirection,
    ) -> Self {
        Self {
            blocks_per_indirection,
            direct_blocks,
            singly_indirected_blocks,
            doubly_indirected_blocks,
            triply_indirected_blocks,
        }
    }

    /// Returns every data block with the indirected blocks.
    #[inline]
    #[must_use]
    pub fn blocks(self) -> (DirectBlocks, SimpleIndirection, DoubleIndirection, TripleIndirection) {
        (self.direct_blocks, self.singly_indirected_blocks, self.doubly_indirected_blocks, self.triply_indirected_blocks)
    }

    /// Returns the complete list of block numbers containing this inode's data (indirect blocks are not considered) in a single
    /// continuous vector.
    #[inline]
    #[must_use]
    pub fn flatten_with_indirection(&self) -> Vec<(u32, (Indirection, u32))> {
        let block_with_indirection = |indirection| {
            // SAFETY: the total number of blocks is stocked on a u32
            move |(index, block): (usize, &u32)| (*block, (indirection, unsafe { u32::try_from(index).unwrap_unchecked() }))
        };

        let mut blocks = self
            .direct_blocks
            .iter()
            .enumerate()
            .map(block_with_indirection(Indirection::Direct))
            .collect_vec();

        blocks.append(
            &mut self
                .singly_indirected_blocks
                .1
                .iter()
                .enumerate()
                .map(block_with_indirection(Indirection::Simple))
                .collect_vec(),
        );

        blocks.append(
            &mut self
                .doubly_indirected_blocks
                .1
                .iter()
                .enumerate()
                .flat_map(|(simple_indirection_index, (_, blocks))| {
                    blocks
                        .iter()
                        .enumerate()
                        .map(|(index, block)| {
                            (
                                *block,
                                (
                                    Indirection::Double,
                                    // SAFETY: the total number of blocks is stocked on a u32
                                    unsafe { u32::try_from(simple_indirection_index).unwrap_unchecked() }
                                        * self.blocks_per_indirection
                                        // SAFETY: the total number of blocks is stocked on a u32
                                        + unsafe { u32::try_from(index).unwrap_unchecked() },
                                ),
                            )
                        })
                        .collect_vec()
                })
                .collect_vec(),
        );

        blocks.append(
            &mut self
                .triply_indirected_blocks
                .1
                .iter()
                .enumerate()
                .flat_map(|(double_indirection_index, (_, indirected_blocks))| {
                    indirected_blocks
                        .iter()
                        .enumerate()
                        .flat_map(|(simple_indirection_index, (_, blocks))| {
                            blocks
                                .iter()
                                .enumerate()
                                .map(|(index, block)| {
                                    (
                                        *block,
                                        (
                                            Indirection::Triple,
                                            // SAFETY: the total number of blocks is stocked on a u32
                                            unsafe { u32::try_from(double_indirection_index).unwrap_unchecked() }
                                                * self.blocks_per_indirection
                                                * self.blocks_per_indirection
                                                // SAFETY: the total number of blocks is stocked on a u32
                                                + unsafe { u32::try_from(simple_indirection_index).unwrap_unchecked() }
                                                    * self.blocks_per_indirection
                                                    // SAFETY: the total number of blocks is stocked on a u32
                                                    + unsafe { u32::try_from(index).unwrap_unchecked() },
                                        ),
                                    )
                                })
                                .collect_vec()
                        })
                        .collect_vec()
                })
                .collect_vec(),
        );

        blocks
    }

    /// Returns the complete list of block numbers containing this inode's data (indirect blocks are not considered) in a single
    /// continuous vector.
    #[inline]
    #[must_use]
    pub fn flatten(&self) -> Vec<u32> {
        self.flatten_with_indirection().into_iter().map(|(block, _)| block).collect_vec()
    }

    /// Returns the indirection and the remaining offset in this indirection to fetch the block at the given `offset`.
    ///
    /// Returns [`None`] if the offset points a block outside the range of this structure.
    #[allow(clippy::suspicious_operation_groupings)]
    #[inline]
    #[must_use]
    pub const fn block_at_offset_remainging_in_indirection(offset: u32, blocks_per_indirection: u32) -> Option<(Indirection, u32)> {
        if offset < 12 {
            Some((Indirection::Direct, offset))
        } else if offset < DBPC + blocks_per_indirection {
            Some((Indirection::Simple, offset - DBPC))
        } else if offset < DBPC + blocks_per_indirection + blocks_per_indirection * blocks_per_indirection {
            Some((Indirection::Double, offset - (DBPC + blocks_per_indirection)))
        } else if offset
            < DBPC
                + blocks_per_indirection
                + blocks_per_indirection * blocks_per_indirection
                + blocks_per_indirection * blocks_per_indirection * blocks_per_indirection
        {
            Some((Indirection::Triple, offset - (DBPC + blocks_per_indirection + blocks_per_indirection * blocks_per_indirection)))
        } else {
            None
        }
    }

    /// Returns the block at the given offset in the given indirection.
    ///
    /// This is easily usable in pair with
    /// [`block_at_offset_remainging_in_indirection`](struct.IndirectedBlocks.html#method.block_at_offset_remainging_in_indirection)
    /// or with [`last_data_block_allocated`](struct.IndirectedBlocks.html#method.last_data_block_allocated).
    #[inline]
    #[must_use]
    pub fn block_at_offset_in_indirection(&self, indirection: Indirection, offset: u32) -> Option<u32> {
        match indirection {
            Indirection::Direct => self.direct_blocks.resolve_indirection(offset, self.blocks_per_indirection),
            Indirection::Simple => self.singly_indirected_blocks.resolve_indirection(offset, self.blocks_per_indirection),
            Indirection::Double => self.doubly_indirected_blocks.resolve_indirection(offset, self.blocks_per_indirection),
            Indirection::Triple => self.triply_indirected_blocks.resolve_indirection(offset, self.blocks_per_indirection),
        }
    }

    /// Returns the block at the given offset.
    #[inline]
    #[must_use]
    pub fn block_at_offset(&self, offset: u32) -> Option<u32> {
        let (indirection, remaining_offset) = Self::block_at_offset_remainging_in_indirection(offset, self.blocks_per_indirection)?;
        self.block_at_offset_in_indirection(indirection, remaining_offset)
    }

    /// Returns the last allocated block of the complete structure, if it exists, with its indirection and its the remaining offset
    /// in the redirection.
    #[inline]
    #[must_use]
    pub fn last_data_block_allocated(&self) -> Option<(u32, (Indirection, u32))> {
        let last_triply_indirected = self
            .triply_indirected_blocks
            .1
            .last()
            .and_then(|(_, doubly_indirected_blocks)| {
                doubly_indirected_blocks.last().map(|(_, singly_indirected_blocks)| {
                    singly_indirected_blocks.last().map(|block| {
                        (
                            // SAFETY: `double_indirection_index < blocks_per_indirection << u32::MAX`
                            unsafe { u32::try_from(self.triply_indirected_blocks.1.len() - 1).unwrap_unchecked() }
                                    * self.blocks_per_indirection
                                    * self.blocks_per_indirection
                                    // SAFETY: `single_indirection_index < blocks_per_indirection << u32::MAX`
                                    + unsafe { u32::try_from(doubly_indirected_blocks.len() - 1).unwrap_unchecked() }
                                        * self.blocks_per_indirection
                                    // SAFETY: `direct_block_index < blocks_per_indirection << u32::MAX`
                                    + unsafe { u32::try_from(singly_indirected_blocks.len() - 1).unwrap_unchecked() },
                            *block,
                        )
                    })
                })
            })
            .flatten();

        if let Some((offset, block)) = last_triply_indirected {
            return Some((block, (Indirection::Triple, offset)));
        }

        let last_doubly_indirected = self.doubly_indirected_blocks.1.last().and_then(|(_, singly_indirected_blocks)| {
            singly_indirected_blocks.last().map(|block| {
                (
                    // SAFETY: `single_indirection_index < blocks_per_indirection << u32::MAX`
                    unsafe { u32::try_from(self.doubly_indirected_blocks.1.len() - 1).unwrap_unchecked() } * self.blocks_per_indirection
                            // SAFETY: `direct_block_index < blocks_per_indirection << u32::MAX`
                            + unsafe { u32::try_from(singly_indirected_blocks.len() - 1).unwrap_unchecked() },
                    *block,
                )
            })
        });

        if let Some((offset, block)) = last_doubly_indirected {
            return Some((block, (Indirection::Double, offset)));
        }

        let last_singly_indirected = self
            .singly_indirected_blocks
            .1
            .last()
            // SAFETY: `direct_block_index < blocks_per_indirection << u32::MAX`
            .map(|block| (unsafe { u32::try_from(self.singly_indirected_blocks.1.len() - 1).unwrap_unchecked() }, *block));

        if let Some((offset, block)) = last_singly_indirected {
            return Some((block, (Indirection::Simple, offset)));
        }

        self.direct_blocks
            .iter()
            .enumerate()
            .last()
            // SAFETY: `direct_block_index < 12 << u32::MAX`
            .map(|(index, block)| (*block, (Indirection::Direct, unsafe { u32::try_from(index).unwrap_unchecked() })))
    }

    /// Returns the total number of data blocks.
    #[inline]
    #[must_use]
    pub fn data_block_count(&self) -> u32 {
        match self.last_data_block_allocated() {
            None => 0,
            Some((_, (indirection, index))) => {
                1 + index
                    + match indirection {
                        Indirection::Direct => 0,
                        Indirection::Simple => DBPC,
                        Indirection::Double => DBPC + self.blocks_per_indirection,
                        Indirection::Triple => {
                            DBPC + self.blocks_per_indirection + self.blocks_per_indirection * self.blocks_per_indirection
                        },
                    }
            },
        }
    }

    /// Returns the number of necessary indirection blocks to have `data_block_count` blocks of data.
    ///
    /// Returns [`None`] if the given number of data blocks cannot fit on this structure.
    #[inline]
    #[must_use]
    pub const fn necessary_indirection_block_count(data_block_count: u32, blocks_per_indirection: u32) -> Option<u32> {
        let Some((indirection, index)) = Self::block_at_offset_remainging_in_indirection(data_block_count, blocks_per_indirection)
        else {
            return None;
        };

        Some(match indirection {
            Indirection::Direct => 0,
            Indirection::Simple => 1,
            Indirection::Double => 1 + 1 + index / blocks_per_indirection + if index % blocks_per_indirection == 0 { 0 } else { 1 },
            Indirection::Triple => {
                1 + 1
                    + blocks_per_indirection
                    + 1
                    + (index / (blocks_per_indirection * blocks_per_indirection)) * (blocks_per_indirection + 1)
                    + if index % (blocks_per_indirection * blocks_per_indirection) == 0 {
                        0
                    } else {
                        let remaining_offset = index % (blocks_per_indirection * blocks_per_indirection);
                        1 + remaining_offset / blocks_per_indirection
                            + if remaining_offset % blocks_per_indirection == 0 { 0 } else { 1 }
                    }
            },
        })
    }

    /// Returns the total number of indirection blocks.
    #[inline]
    #[must_use]
    pub fn indirection_block_count(&self) -> u32 {
        // SAFETY: self contains the block at index `data_block_count - 1`
        unsafe { Self::necessary_indirection_block_count(self.data_block_count(), self.blocks_per_indirection).unwrap_unchecked() }
    }

    /// Appends the given `blocks` to the indirection blocks.
    ///
    /// The given blocks are used **both for data and indirection blocks**.
    ///
    /// If more blocks than necessary to complete all the structure, only the first one will be used.
    #[inline]
    pub fn append_blocks(&mut self, blocks: &[u32]) {
        let blocks_per_indirection = self.blocks_per_indirection as usize;

        let blocks_iterator = &mut blocks.iter();

        if self.direct_blocks.len() < DBPC as usize {
            self.direct_blocks
                .append(&mut blocks_iterator.take(DBPC as usize - self.direct_blocks.len()).copied().collect_vec());
        }

        if self.singly_indirected_blocks.0 == 0 {
            self.singly_indirected_blocks.0 = blocks_iterator.next().copied().unwrap_or_default();
        }

        if blocks_iterator.is_empty() {
            return;
        }

        if self.singly_indirected_blocks.1.len() < blocks_per_indirection {
            self.singly_indirected_blocks.1.append(
                &mut blocks_iterator
                    .take(blocks_per_indirection - self.singly_indirected_blocks.1.len())
                    .copied()
                    .collect_vec(),
            );
        }

        if self.doubly_indirected_blocks.0 == 0 {
            self.doubly_indirected_blocks.0 = blocks_iterator.next().copied().unwrap_or_default();
        }

        if blocks_iterator.is_empty() {
            return;
        }

        if self.doubly_indirected_blocks.1.len() <= blocks_per_indirection {
            match self.doubly_indirected_blocks.1.last_mut() {
                None => {},
                Some((_, data_blocks)) => {
                    if data_blocks.len() < blocks_per_indirection {
                        data_blocks
                            .append(&mut blocks_iterator.take(blocks_per_indirection - data_blocks.len()).copied().collect_vec());
                    }
                },
            }

            while self.doubly_indirected_blocks.1.len() < blocks_per_indirection && let Some(block) = blocks_iterator.next()  {
                let indirection_block = (*block, blocks_iterator.take(blocks_per_indirection).copied().collect_vec());
                self.doubly_indirected_blocks.1.push(indirection_block);
            }
        }

        if self.triply_indirected_blocks.0 == 0 {
            self.triply_indirected_blocks.0 = blocks_iterator.next().copied().unwrap_or_default();
        }

        if blocks_iterator.is_empty() {
            return;
        }

        if self.triply_indirected_blocks.1.len() <= blocks_per_indirection {
            match self.triply_indirected_blocks.1.last_mut() {
                None => {},
                Some((_, indirected_blocks)) => {
                    if indirected_blocks.len() < blocks_per_indirection {
                        match indirected_blocks.last_mut() {
                            None => {},
                            Some((_, data_blocks)) => {
                                if data_blocks.len() < blocks_per_indirection {
                                    data_blocks.append(
                                        &mut blocks_iterator
                                            .take(blocks_per_indirection - data_blocks.len())
                                            .copied()
                                            .collect_vec(),
                                    );
                                }
                            },
                        }

                        while indirected_blocks.len() < blocks_per_indirection && let Some(block) = blocks_iterator.next() {
                            let indirection_block = (*block, blocks_iterator.take(blocks_per_indirection).copied().collect_vec());
                            indirected_blocks.push(indirection_block);
                        }
                    }
                },
            }

            while self.triply_indirected_blocks.1.len() < blocks_per_indirection && let Some(block) = blocks_iterator.next() {
                let mut doubly_indirection_block = (*block, Vec::new());
                while let Some(block) = blocks_iterator.next() && doubly_indirection_block.1.len() < blocks_per_indirection {
                    let indirection_block = (*block, blocks_iterator.take(blocks_per_indirection).copied().collect_vec());
                    doubly_indirection_block.1.push(indirection_block);
                }
                self.triply_indirected_blocks.1.push(doubly_indirection_block);
            }
        }
    }

    /// Returns the [`SymmetricDifference`] between `self` and the [`IndirectedBlocks`] obtained after adding `blocks` to `self`.
    #[inline]
    #[must_use]
    pub(crate) fn simulate_append_blocks(&self, blocks: &[u32]) -> SymmetricDifference<DBPC> {
        let Some((_, (last_indirection, last_index))) = self.last_data_block_allocated() else {
            return SymmetricDifference(Self {
                blocks_per_indirection: self.blocks_per_indirection,
                direct_blocks: Vec::new(),
                singly_indirected_blocks: (0, Vec::new()),
                doubly_indirected_blocks: (0, Vec::new()),
                triply_indirected_blocks: (0, Vec::new()),
            });
        };

        let mut indirection = self.clone();
        indirection.append_blocks(blocks);

        match last_indirection {
            Indirection::Direct => {
                for i in 0..=last_index as usize {
                    if let Some(block) = indirection.direct_blocks.get_mut(i) {
                        *block = 0;
                    };
                }
            },
            Indirection::Simple => {
                indirection.direct_blocks = Vec::new();
                for i in 0..=last_index as usize {
                    if let Some(block) = indirection.singly_indirected_blocks.1.get_mut(i) {
                        *block = 0;
                    }
                }
                if last_index + 1 == self.blocks_per_indirection {
                    indirection.singly_indirected_blocks.0 = 0;
                }
            },
            Indirection::Double => {
                indirection.direct_blocks = Vec::new();
                indirection.singly_indirected_blocks.0 = 0;
                indirection.singly_indirected_blocks.1 = Vec::new();

                for i in 0..(last_index / self.blocks_per_indirection) as usize {
                    if let Some(simple_block_indirection) = indirection.doubly_indirected_blocks.1.get_mut(i) {
                        simple_block_indirection.0 = 0;
                        simple_block_indirection.1 = Vec::new();
                    }
                }

                let last_indirection_index = (last_index / self.blocks_per_indirection) as usize;
                if let Some(simple_block_indirection) = indirection.doubly_indirected_blocks.1.get_mut(last_indirection_index) {
                    if (last_index + 1) % self.blocks_per_indirection == 0 {
                        simple_block_indirection.0 = 0;
                        simple_block_indirection.1 = Vec::new();
                    } else {
                        for j in 0..=(last_index % self.blocks_per_indirection) as usize {
                            if let Some(block) = simple_block_indirection.1.get_mut(j) {
                                *block = 0;
                            }
                        }
                    }
                };
            },
            Indirection::Triple => {
                indirection.direct_blocks = Vec::new();
                indirection.singly_indirected_blocks.0 = 0;
                indirection.singly_indirected_blocks.1 = Vec::new();
                indirection.doubly_indirected_blocks.0 = 0;
                indirection.doubly_indirected_blocks.1 = Vec::new();

                for i in 0..(last_index / (self.blocks_per_indirection * self.blocks_per_indirection)) as usize {
                    if let Some(double_block_indirection) = indirection.triply_indirected_blocks.1.get_mut(i) {
                        double_block_indirection.0 = 0;
                        double_block_indirection.1 = Vec::new();
                    }
                }

                let last_double_indirection_index =
                    (last_index / (self.blocks_per_indirection * self.blocks_per_indirection)) as usize;
                if let Some(double_block_indirection) =
                    indirection.triply_indirected_blocks.1.get_mut(last_double_indirection_index)
                {
                    if (last_index + 1) % (self.blocks_per_indirection * self.blocks_per_indirection) == 0 {
                        double_block_indirection.0 = 0;
                        double_block_indirection.1 = Vec::new();
                    } else {
                        let last_indirection_index = last_double_indirection_index / self.blocks_per_indirection as usize;
                        for j in 0..=last_indirection_index {
                            if let Some(simple_block_indirection) = double_block_indirection.1.get_mut(j) {
                                simple_block_indirection.0 = 0;
                                simple_block_indirection.1 = Vec::new();
                            }
                        }

                        if let Some(simple_block_indirection) = double_block_indirection.1.get_mut(last_indirection_index + 1) {
                            if (last_index + 1) % self.blocks_per_indirection == 0 {
                                simple_block_indirection.0 = 0;
                                simple_block_indirection.1 = Vec::new();
                            } else {
                                for j in 0..=(last_index % self.blocks_per_indirection) as usize {
                                    if let Some(block) = simple_block_indirection.1.get_mut(j) {
                                        *block = 0;
                                    }
                                }
                            }
                        }
                    }
                };
            },
        }

        SymmetricDifference(indirection)
    }
}

/// Represents the symmetric difference between two [`IndirectedBlocks`].
///
/// This can be very useful in the manipulation of [`IndirectedBlocks`] during the addition or the removal of some indirection
/// blocks.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SymmetricDifference<const DBPC: u32>(IndirectedBlocks<DBPC>);

#[cfg(test)]
mod test {
    use alloc::vec;

    use super::{IndirectedBlocks, Indirection};
    use crate::fs::ext2::indirection::SymmetricDifference;
    use crate::fs::ext2::inode::DIRECT_BLOCK_POINTER_COUNT;

    #[test]
    fn direct_indirection() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7],
            (0, vec![]),
            (0, vec![]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.block_at_offset(3), Some(4));
    }

    #[test]
    fn simple_indirection() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            1_024,
            vec![1; 12],
            (1, vec![1, 1, 2, 1, 1]),
            (0, vec![]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.block_at_offset(14), Some(2));
    }

    #[test]
    fn double_indirection() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1, 2, 1, 1, 1]), (1, vec![1; 3])]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.block_at_offset(3), Some(1));
        assert_eq!(indirected_blocks.block_at_offset(27), Some(1));
        assert_eq!(indirected_blocks.block_at_offset(28), Some(2));
        assert_eq!(indirected_blocks.block_at_offset(1_000), None);
    }

    #[test]
    fn triple_indirection() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
            (1, vec![
                (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
                (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
                (1, vec![(1, vec![1; 5]), (1, vec![2, 1, 1, 1, 1]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
            ]),
        );
        assert_eq!(indirected_blocks.block_at_offset(97), Some(2));
    }

    #[test]
    fn last_data_block_allocated() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7],
            (0, vec![]),
            (0, vec![]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.last_data_block_allocated(), Some((7, (Indirection::Direct, 6))));

        let indirected_blocks =
            IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(1_024, vec![0; 12], (0, vec![0, 0, 1]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.last_data_block_allocated(), Some((1, (Indirection::Simple, 2))));

        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![0; 12],
            (0, vec![0; 5]),
            (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0, 1])]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.last_data_block_allocated(), Some((1, (Indirection::Double, 11))));

        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![0; 12],
            (0, vec![0; 5]),
            (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5])]),
            (0, vec![
                (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5])]),
                (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5])]),
                (1, vec![(0, vec![0; 5]), (0, vec![1])]),
            ]),
        );
        assert_eq!(indirected_blocks.last_data_block_allocated(), Some((1, (Indirection::Triple, 55))));
    }

    #[test]
    fn block_counts() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7],
            (0, vec![]),
            (0, vec![]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.data_block_count(), 7);
        assert_eq!(indirected_blocks.indirection_block_count(), 0);
        assert_eq!(IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::necessary_indirection_block_count(7, 5), Some(0));

        let indirected_blocks =
            IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(1_024, vec![1; 12], (1, vec![1, 1, 1]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.data_block_count(), 15);
        assert_eq!(indirected_blocks.indirection_block_count(), 1);
        assert_eq!(IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::necessary_indirection_block_count(15, 5), Some(1));

        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1, 1])]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.data_block_count(), 29);
        assert_eq!(indirected_blocks.indirection_block_count(), 5);
        assert_eq!(IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::necessary_indirection_block_count(29, 5), Some(5));

        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
            (1, vec![
                (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
                (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
                (1, vec![(1, vec![1; 5]), (1, vec![1; 5])]),
            ]),
        );
        assert_eq!(indirected_blocks.data_block_count(), 102);
        assert_eq!(indirected_blocks.indirection_block_count(), 23);
        assert_eq!(IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::necessary_indirection_block_count(102, 5), Some(23));
    }

    #[test]
    fn append_blocks() {
        let mut indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7],
            (0, vec![]),
            (0, vec![]),
            (0, vec![]),
        );
        let indirected_blocks_after_append_1 = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
            (0, vec![]),
            (0, vec![]),
            (0, vec![]),
        );
        let indirected_blocks_after_append_2 = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
            (13, vec![14]),
            (0, vec![]),
            (0, vec![]),
        );

        indirected_blocks.append_blocks(&[8, 9, 10, 11]);
        assert_eq!(indirected_blocks, indirected_blocks_after_append_1);
        indirected_blocks.append_blocks(&[12, 13, 14]);
        assert_eq!(indirected_blocks, indirected_blocks_after_append_2);

        let mut indirected_blocks =
            IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(5, vec![1; 12], (1, vec![1, 1, 1]), (0, vec![]), (0, vec![]));
        let indirected_blocks_after_append_1 =
            IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(5, vec![1; 12], (1, vec![1, 1, 1, 2, 2]), (2, vec![]), (0, vec![]));
        let indirected_blocks_after_append_2 = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1, 1, 1, 2, 2]),
            (2, vec![(3, vec![3; 5]), (3, vec![])]),
            (0, vec![]),
        );

        indirected_blocks.append_blocks(&[2; 3]);
        assert_eq!(indirected_blocks, indirected_blocks_after_append_1);
        indirected_blocks.append_blocks(&[3; 7]);
        assert_eq!(indirected_blocks, indirected_blocks_after_append_2);

        let mut indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1, 1])]),
            (0, vec![]),
        );
        let indirected_blocks_after_append = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1, 1, 2, 2, 2]), (2, vec![2; 5]), (2, vec![2; 5])]),
            (2, vec![(2, vec![(2, vec![2; 3])])]),
        );

        indirected_blocks.append_blocks(&[2; 21]);
        assert_eq!(indirected_blocks, indirected_blocks_after_append);
    }

    #[test]
    fn flatten() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7],
            (0, vec![]),
            (0, vec![]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.flatten_with_indirection(), vec![
            (1, (Indirection::Direct, 0)),
            (2, (Indirection::Direct, 1)),
            (3, (Indirection::Direct, 2)),
            (4, (Indirection::Direct, 3)),
            (5, (Indirection::Direct, 4)),
            (6, (Indirection::Direct, 5)),
            (7, (Indirection::Direct, 6))
        ]);

        let indirected_blocks =
            IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(5, vec![1; 12], (2, vec![3, 3, 3]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.flatten_with_indirection(), vec![
            (1, (Indirection::Direct, 0)),
            (1, (Indirection::Direct, 1)),
            (1, (Indirection::Direct, 2)),
            (1, (Indirection::Direct, 3)),
            (1, (Indirection::Direct, 4)),
            (1, (Indirection::Direct, 5)),
            (1, (Indirection::Direct, 6)),
            (1, (Indirection::Direct, 7)),
            (1, (Indirection::Direct, 8)),
            (1, (Indirection::Direct, 9)),
            (1, (Indirection::Direct, 10)),
            (1, (Indirection::Direct, 11)),
            (3, (Indirection::Simple, 0)),
            (3, (Indirection::Simple, 1)),
            (3, (Indirection::Simple, 2))
        ]);
    }

    #[test]
    fn simulate_append_blocks() {
        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1, 2, 3, 4, 5, 6, 7],
            (0, vec![]),
            (0, vec![]),
            (0, vec![]),
        );
        assert_eq!(
            indirected_blocks.simulate_append_blocks(&[8, 9, 10]),
            SymmetricDifference(IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
                5,
                vec![0, 0, 0, 0, 0, 0, 0, 8, 9, 10],
                (0, vec![]),
                (0, vec![]),
                (0, vec![])
            ))
        );

        let indirected_blocks =
            IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(5, vec![1; 12], (1, vec![1, 1, 1]), (0, vec![]), (0, vec![]));
        assert_eq!(
            indirected_blocks.simulate_append_blocks(&[2, 3, 4, 5]),
            SymmetricDifference(IndirectedBlocks::new(5, vec![], (1, vec![0, 0, 0, 2, 3]), (4, vec![(5, vec![])]), (0, vec![])))
        );

        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1, 1, 1, 2, 2]),
            (2, vec![(3, vec![3; 5]), (3, vec![3])]),
            (0, vec![]),
        );
        assert_eq!(
            indirected_blocks.simulate_append_blocks(&[4, 5, 6, 7, 8, 9, 10]),
            SymmetricDifference(IndirectedBlocks::new(
                5,
                vec![],
                (0, vec![]),
                (2, vec![(0, vec![]), (3, vec![0, 4, 5, 6, 7]), (8, vec![9, 10])]),
                (0, vec![])
            ))
        );

        let indirected_blocks = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1, 1, 2, 2, 2]), (2, vec![2; 5]), (2, vec![2; 5])]),
            (2, vec![(2, vec![(2, vec![2; 5]), (2, vec![2; 3])])]),
        );
        assert_eq!(
            indirected_blocks.simulate_append_blocks(&[3, 4, 5, 6, 7, 8]),
            SymmetricDifference(IndirectedBlocks::new(
                5,
                vec![],
                (0, vec![]),
                (0, vec![]),
                (2, vec![(2, vec![(0, vec![]), (2, vec![0, 0, 0, 3, 4]), (5, vec![6, 7, 8])])])
            ))
        );
    }
}
