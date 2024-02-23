//! Manipulation of indirection in ext2, for the major part for inodes' blocks.
//!
//! See [this Wikipedia section](https://en.wikipedia.org/wiki/Ext2#Inodes) for more information.

use alloc::vec::Vec;

use itertools::Itertools;

use super::inode::DIRECT_BLOCK_POINTER_COUNT;

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
#[derive(Debug)]
pub struct IndirectedBlocks {
    /// Number of blocks contained in each indirection.
    ///
    /// In ext2 filesystems, this always should be equal to `superblock.block_size() / 4`.
    blocks_per_indirection: u32,

    /// The direct block numbers.
    direct_blocks: DirectBlocks,

    /// The singly indirected block numbers.
    singly_indirected_blocks: (u32, Vec<u32>),

    /// The doubly indirected block numbers.
    doubly_indirected_blocks: DoubleIndirection,

    /// The triply indirected block numbers.
    triply_indirected_blocks: TripleIndirection,
}

impl IndirectedBlocks {
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
    pub fn flatten(&self) -> Vec<u32> {
        let mut blocks = self.direct_blocks.clone();

        blocks.append(&mut self.singly_indirected_blocks.1.clone());
        blocks.append(
            &mut self
                .doubly_indirected_blocks
                .1
                .clone()
                .into_iter()
                .flat_map(|(_, blocks)| blocks)
                .collect_vec(),
        );
        blocks.append(
            &mut self
                .triply_indirected_blocks
                .1
                .clone()
                .into_iter()
                .flat_map(|(_, indirected_blocks)| indirected_blocks.into_iter().flat_map(|(_, blocks)| blocks).collect_vec())
                .collect_vec(),
        );

        blocks
    }

    /// Returns the indirection and the remaining offset in this indirection to fetch the block at the given `offset`.
    #[allow(clippy::suspicious_operation_groupings)]
    #[inline]
    #[must_use]
    pub const fn block_at_offset_remainging_in_indirection(offset: u32, blocks_per_indirection: u32) -> Option<(Indirection, u32)> {
        if offset < 12 {
            Some((Indirection::Direct, offset))
        } else if offset < DIRECT_BLOCK_POINTER_COUNT + blocks_per_indirection {
            Some((Indirection::Simple, offset - DIRECT_BLOCK_POINTER_COUNT))
        } else if offset < DIRECT_BLOCK_POINTER_COUNT + blocks_per_indirection + blocks_per_indirection * blocks_per_indirection {
            Some((Indirection::Double, offset - (DIRECT_BLOCK_POINTER_COUNT + blocks_per_indirection)))
        } else if offset
            < DIRECT_BLOCK_POINTER_COUNT
                + blocks_per_indirection
                + blocks_per_indirection * blocks_per_indirection
                + blocks_per_indirection * blocks_per_indirection * blocks_per_indirection
        {
            Some((
                Indirection::Triple,
                offset - (DIRECT_BLOCK_POINTER_COUNT + blocks_per_indirection + blocks_per_indirection * blocks_per_indirection),
            ))
        } else {
            None
        }
    }

    /// Returns the block at the given offset in the given indirection.
    ///
    /// This is easily usable in pair with
    /// [`block_at_offset_remainging_in_indirection`](struct.IndirectedBlocks.html#method.block_at_offset_remainging_in_indirection)
    /// or with [`last_block_allocated`](struct.IndirectedBlocks.html#method.last_block_allocated).
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
    pub fn last_block_allocated(&self) -> Option<(u32, (Indirection, u32))> {
        let last_triply_indirected = self
            .triply_indirected_blocks
            .1
            .iter()
            .enumerate()
            .last()
            .and_then(|(double_indirection_index, (_, doubly_indirected_blocks))| {
                doubly_indirected_blocks.iter().enumerate().last().map(
                    |(single_indirection_index, (_, singly_indirected_blocks))| {
                        singly_indirected_blocks.iter().enumerate().last().map(|(direct_block_index, block)| {
                            (
                                // SAFETY: `double_indirection_index < blocks_per_indirection << u32::MAX`
                                unsafe { u32::try_from(double_indirection_index).unwrap_unchecked() }
                                    * self.blocks_per_indirection
                                    * self.blocks_per_indirection
                                    // SAFETY: `single_indirection_index < blocks_per_indirection << u32::MAX`
                                    + unsafe { u32::try_from(single_indirection_index).unwrap_unchecked() }
                                        * self.blocks_per_indirection
                                    // SAFETY: `direct_block_index < blocks_per_indirection << u32::MAX`
                                    + unsafe { u32::try_from(direct_block_index).unwrap_unchecked() },
                                *block,
                            )
                        })
                    },
                )
            })
            .flatten();

        if let Some((offset, block)) = last_triply_indirected {
            return Some((block, (Indirection::Triple, offset)));
        }

        let last_doubly_indirected = self.doubly_indirected_blocks.1.iter().enumerate().last().and_then(
            |(single_indirection_index, (_, singly_indirected_blocks))| {
                singly_indirected_blocks.iter().enumerate().last().map(|(direct_block_index, block)| {
                    (
                        // SAFETY: `single_indirection_index < blocks_per_indirection << u32::MAX`
                        unsafe { u32::try_from(single_indirection_index).unwrap_unchecked() } * self.blocks_per_indirection
                            // SAFETY: `direct_block_index < blocks_per_indirection << u32::MAX`
                            + unsafe { u32::try_from(direct_block_index).unwrap_unchecked() },
                        *block,
                    )
                })
            },
        );

        if let Some((offset, block)) = last_doubly_indirected {
            return Some((block, (Indirection::Double, offset)));
        }

        let last_singly_indirected = self
            .singly_indirected_blocks
            .1
            .iter()
            .enumerate()
            .last()
            // SAFETY: `direct_block_index < blocks_per_indirection << u32::MAX`
            .map(|(direct_block_index, block)| (unsafe { u32::try_from(direct_block_index).unwrap_unchecked() }, *block));

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
        match self.last_block_allocated() {
            Some((_, (indirection, index))) => {
                1 + index
                    + match indirection {
                        Indirection::Direct => 0,
                        Indirection::Simple => DIRECT_BLOCK_POINTER_COUNT,
                        Indirection::Double => DIRECT_BLOCK_POINTER_COUNT + self.blocks_per_indirection,
                        Indirection::Triple => {
                            DIRECT_BLOCK_POINTER_COUNT
                                + self.blocks_per_indirection
                                + self.blocks_per_indirection * self.blocks_per_indirection
                        },
                    }
            },
            None => 0,
        }
    }

    /// Returns the total number of indirection blocks.
    #[inline]
    #[must_use]
    pub fn indirection_block_count(&self) -> u32 {
        match self.last_block_allocated() {
            None => 0,
            Some((_, (indirection, index))) => match indirection {
                Indirection::Direct => 0,
                Indirection::Simple => 1,
                Indirection::Double => {
                    1 + 1 + index / self.blocks_per_indirection + u32::from(index % self.blocks_per_indirection != 0)
                },
                Indirection::Triple => {
                    1 + 1
                        + self.blocks_per_indirection
                        + 1
                        + (index * (self.blocks_per_indirection + 1)) / (self.blocks_per_indirection * self.blocks_per_indirection)
                        + if index % (self.blocks_per_indirection * self.blocks_per_indirection) == 0 {
                            0
                        } else {
                            let remaining_offset = index % (self.blocks_per_indirection * self.blocks_per_indirection);
                            1 + remaining_offset / self.blocks_per_indirection
                                + u32::from(remaining_offset % self.blocks_per_indirection != 0)
                        }
                },
            },
        }
    }
}

#[cfg(test)]
mod test {
    use alloc::vec;

    use super::{IndirectedBlocks, Indirection};

    #[test]
    fn direct_indirection() {
        let indirected_blocks = IndirectedBlocks::new(5, vec![1, 2, 3, 4, 5, 6, 7], (0, vec![]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.block_at_offset(3), Some(4));
    }

    #[test]
    fn simple_indirection() {
        let indirected_blocks = IndirectedBlocks::new(1_024, vec![1; 12], (1, vec![1, 1, 2, 1, 1]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.block_at_offset(14), Some(2));
    }

    #[test]
    fn double_indirection() {
        let indirected_blocks = IndirectedBlocks::new(
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
        let indirected_blocks = IndirectedBlocks::new(
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
    fn last_block_allocated() {
        let indirected_blocks = IndirectedBlocks::new(5, vec![1, 2, 3, 4, 5, 6, 7], (0, vec![]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.last_block_allocated(), Some((7, (Indirection::Direct, 6))));

        let indirected_blocks = IndirectedBlocks::new(1_024, vec![0; 12], (0, vec![0, 0, 1]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.last_block_allocated(), Some((1, (Indirection::Simple, 2))));

        let indirected_blocks = IndirectedBlocks::new(
            5,
            vec![0; 12],
            (0, vec![0; 5]),
            (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0, 1])]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.last_block_allocated(), Some((1, (Indirection::Double, 11))));

        let indirected_blocks = IndirectedBlocks::new(
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
        assert_eq!(indirected_blocks.last_block_allocated(), Some((1, (Indirection::Triple, 55))));
    }

    #[test]
    fn block_counts() {
        let indirected_blocks = IndirectedBlocks::new(5, vec![1, 2, 3, 4, 5, 6, 7], (0, vec![]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.data_block_count(), 7);
        assert_eq!(indirected_blocks.indirection_block_count(), 0);

        let indirected_blocks = IndirectedBlocks::new(1_024, vec![1; 12], (1, vec![1, 1, 1]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.data_block_count(), 15);
        assert_eq!(indirected_blocks.indirection_block_count(), 1);

        let indirected_blocks = IndirectedBlocks::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1, 1])]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.data_block_count(), 29);
        assert_eq!(indirected_blocks.indirection_block_count(), 5);

        let indirected_blocks = IndirectedBlocks::new(
            5,
            vec![1; 12],
            (1, vec![1; 5]),
            (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
            (1, vec![
                (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
                (1, vec![(1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5]), (1, vec![1; 5])]),
                (1, vec![(1, vec![1; 5]), (1, vec![1])]),
            ]),
        );
        assert_eq!(indirected_blocks.data_block_count(), 98);
        assert_eq!(indirected_blocks.indirection_block_count(), 23);
    }
}
