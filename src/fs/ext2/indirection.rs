//! Manipulation of indirection in ext2, for the major part for inodes' blocks.
//!
//! See [this Wikipedia section](https://en.wikipedia.org/wiki/Ext2#Inodes) for more information.

use alloc::vec::Vec;

use itertools::Itertools;

/// Block indirections.
///
/// See [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#i-block) for more information.
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
    fn resolve_indirection(&self, offset: u32, blocks_per_group: u32) -> Option<u32>;
}

impl Indirected for DirectBlocks {
    #[inline]
    fn resolve_indirection(&self, offset: u32, _blocks_per_group: u32) -> Option<u32> {
        self.get(offset as usize).copied()
    }
}

impl Indirected for SimpleIndirection {
    #[inline]
    fn resolve_indirection(&self, offset: u32, _blocks_per_group: u32) -> Option<u32> {
        self.1.get(offset as usize).copied()
    }
}

impl Indirected for DoubleIndirection {
    #[inline]
    fn resolve_indirection(&self, offset: u32, blocks_per_group: u32) -> Option<u32> {
        let double_indirection_index = offset / blocks_per_group;
        let simple_indirection_index = offset % blocks_per_group;
        self.1.get(double_indirection_index as usize).and_then(|simple_indirection_block| {
            simple_indirection_block.1.resolve_indirection(simple_indirection_index, blocks_per_group)
        })
    }
}

impl Indirected for TripleIndirection {
    #[inline]
    fn resolve_indirection(&self, offset: u32, blocks_per_group: u32) -> Option<u32> {
        let triple_indirection_index = offset / (blocks_per_group * blocks_per_group);
        let double_indirection_index = offset % (blocks_per_group * blocks_per_group);
        self.1.get(triple_indirection_index as usize).and_then(|double_indirection_block| {
            double_indirection_block.resolve_indirection(double_indirection_index, blocks_per_group)
        })
    }
}

/// Type for data blocks in an inode.
///
/// Only contains the real data blocks (with a number different than 0).
#[derive(Debug)]
pub struct IndirectedBlocks {
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
        direct_blocks: DirectBlocks,
        singly_indirected_blocks: SimpleIndirection,
        doubly_indirected_blocks: DoubleIndirection,
        triply_indirected_blocks: TripleIndirection,
    ) -> Self {
        Self {
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

    /// Returns the indirection and the remaining offset in this indirection.
    #[inline]
    #[must_use]
    pub const fn block_offset_remainging_indirection(offset: u32, blocks_per_group: u32) -> Option<(Indirection, u32)> {
        if offset < 12 {
            Some((Indirection::Direct, offset))
        } else if offset < 12 + blocks_per_group {
            Some((Indirection::Simple, offset - 12))
        } else if offset < 12 + blocks_per_group + blocks_per_group * blocks_per_group {
            Some((Indirection::Double, offset - (12 + blocks_per_group)))
        } else if offset
            < 12 + blocks_per_group + blocks_per_group * blocks_per_group + blocks_per_group * blocks_per_group * blocks_per_group
        {
            Some((Indirection::Triple, offset - (12 + blocks_per_group + blocks_per_group * blocks_per_group)))
        } else {
            None
        }
    }

    /// Returns the block at the given offset.
    #[inline]
    #[must_use]
    pub fn block_offset(&self, offset: u32, blocks_per_group: u32) -> Option<u32> {
        let (indirection, remaining_offset) = Self::block_offset_remainging_indirection(offset, blocks_per_group)?;
        match indirection {
            Indirection::Direct => self.direct_blocks.resolve_indirection(remaining_offset, blocks_per_group),
            Indirection::Simple => self.singly_indirected_blocks.resolve_indirection(remaining_offset, blocks_per_group),
            Indirection::Double => self.doubly_indirected_blocks.resolve_indirection(remaining_offset, blocks_per_group),
            Indirection::Triple => self.triply_indirected_blocks.resolve_indirection(remaining_offset, blocks_per_group),
        }
    }
}

#[cfg(test)]
mod test {
    use alloc::vec;

    use super::IndirectedBlocks;

    #[test]
    fn direct_indirection() {
        let indirected_blocks = IndirectedBlocks::new(vec![1, 2, 3, 4, 5, 6, 7], (0, vec![]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.block_offset(3, 5), Some(4));
    }

    #[test]
    fn simple_indirection() {
        let indirected_blocks = IndirectedBlocks::new(vec![0; 12], (0, vec![0, 0, 1, 0, 0]), (0, vec![]), (0, vec![]));
        assert_eq!(indirected_blocks.block_offset(14, 1_024), Some(1));
    }

    #[test]
    fn double_indirection() {
        let indirected_blocks = IndirectedBlocks::new(
            vec![0; 12],
            (0, vec![0; 5]),
            (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0, 1, 0, 0, 0]), (0, vec![0; 3])]),
            (0, vec![]),
        );
        assert_eq!(indirected_blocks.block_offset(3, 5), Some(0));
        assert_eq!(indirected_blocks.block_offset(27, 5), Some(0));
        assert_eq!(indirected_blocks.block_offset(28, 5), Some(1));
        assert_eq!(indirected_blocks.block_offset(1_000, 5), None);
    }

    #[test]
    fn triple_indirection() {
        let indirected_blocks = IndirectedBlocks::new(
            vec![0; 12],
            (0, vec![0; 5]),
            (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5])]),
            (0, vec![
                (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5])]),
                (0, vec![(0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5])]),
                (1, vec![(0, vec![0; 5]), (0, vec![1, 0, 0, 0, 0]), (0, vec![0; 5]), (0, vec![0; 5]), (0, vec![0; 5])]),
            ]),
        );
        assert_eq!(indirected_blocks.block_offset(97, 5), Some(1));
    }
}
