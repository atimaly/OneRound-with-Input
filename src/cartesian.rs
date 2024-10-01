pub mod cartesian {
    use anyhow::{anyhow, Result};
    use itertools::structs::MultiProduct;
    use itertools::Itertools;
    use permutator::CartesianProductIterator;
    use round_eliminator_lib::algorithms::multisets_pairing::{Comb, Pairings};
    use round_eliminator_lib::group::{Group, GroupType, Label};
    use round_eliminator_lib::line::Line;
    use round_eliminator_lib::part::Part;
    use round_eliminator_lib::problem::{self, Problem};
    use std::collections::{HashMap, HashSet};
    use std::iter::Peekable;
    use std::iter::{Map, Repeat, Take};
    use std::ops::Range;
    use streaming_iterator::StreamingIterator;

    /// Because CartesianProductIterator based on references to the original object
    /// One can not simply just  return a CartesianProductIterator// Assuming you have already defined CartesianProductIterator somewhere
    /// Function that returns an iterator over the Cartesian product of ranges [0..a_1-1], [0..a_2-1], ..., [0..a_n-1]
    pub fn cartesian_product_ranges(a: Vec<usize>) -> MultiProduct<Range<usize>> {
        // Step 1: Create a vector of ranges based on the elements of `a`
        let ranges: Vec<std::ops::Range<usize>> = a.iter().map(|&x| 0..x).collect();

        // Step 2: Return the iterator of the Cartesian product
        ranges.into_iter().multi_cartesian_product()
    }
}
