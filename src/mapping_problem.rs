pub mod mapping_problem {
    use crate::cartesian;
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

    /// Given two LCl problems (input, output) it creates between the node configurations of
    /// the input and the output problems a surjective function.
    /// The Iterator trait is also implemented for the struct.
    #[derive(Debug, Clone)]
    pub struct ConfigurationsMapping {
        number_of_input_configurations: usize,
        number_of_output_configurations: usize,
        mappings: Peekable<MultiProduct<Range<usize>>>,
    }

    impl ConfigurationsMapping {
        pub fn new(in_numb: usize, out_numb: usize) -> ConfigurationsMapping {
            ConfigurationsMapping {
                number_of_input_configurations: in_numb,
                number_of_output_configurations: out_numb,
                mappings: std::iter::repeat(0..out_numb)
                    .take(in_numb)
                    .multi_cartesian_product()
                    .peekable(),
            }
        }

        /*pub fn current_mapping(&mut self) -> Option<&Vec<usize>> {
            self.mappings.peek()
        }*/
    }

    impl Iterator for ConfigurationsMapping {
        type Item = Vec<usize>;

        fn next(&mut self) -> Option<Self::Item> {
            self.mappings.next()
        }
    }

    impl Default for ConfigurationsMapping {
        fn default() -> ConfigurationsMapping {
            ConfigurationsMapping {
                number_of_input_configurations: 0,
                number_of_output_configurations: 0,
                mappings: std::iter::repeat(0..0)
                    .take(0)
                    .multi_cartesian_product()
                    .peekable(),
            }
        }
    }

    /// Given two LCl problems (input, output) it creates between the label sets of
    /// the input and the output problems a function.
    /// The Iterator trait is also implemented for the struct.
    #[derive(Debug, Clone)]
    pub struct LabelMapping<'a> {
        /// The problem on which we are creating the LabelMapping
        mapping_problem: &'a MappingProblem,
        /// The current mapping of the input lables to the output ones.
        mappings: Peekable<MultiProduct<Range<usize>>>,
        /// Pairings of lables that make sense with the from_id input node config and to_id output_node_config
        pairings: Vec<(Pairings, usize, usize)>,
        /// For every pairings element all of the possible ones that we need
        all_good_pairings: Vec<Vec<Vec<usize>>>,
        /// Every good_pairings variable it stores the HashSet equivalent of it
        /// So Where does every label goes to in the given node config to node config instance.
        /// So every input node config has a Hashmap which stores every possible pairing matching's result
        /// as a Hashset
        /// Ex. A A X is mapped to B D C then hashmaped_good_pairings[A A X] = [ [{A: {B,D}, X: {C}}], [{A: {D,C}, X:{D}}], etc. ]
        hashmaped_good_pairings: Vec<Vec<HashMap<Group, HashSet<Group>>>>,
    }

    impl<'a> LabelMapping<'a> {
        /// The current mapping of the input_all_node_config ith Line element to the configurations_map[i]th Line in output_all_node_config
        pub fn new(
            mapping_problem: &'a MappingProblem,
            input_all_node_config: &Vec<Line>,
            output_all_node_config: &Vec<Line>,
            configurations_map: &Vec<usize>,
        ) -> Result<LabelMapping<'a>> {
            let mut pairs: Vec<(Pairings, usize, usize)> = vec![];
            let line_to_counts = |line: &Line, starvalue: usize| -> Vec<usize> {
                line.parts
                    .iter()
                    .map(|part| match part.gtype {
                        //GroupType::ONE => 1,
                        GroupType::Many(x) => x as usize,
                        GroupType::Star => starvalue,
                    })
                    .collect()
            };

            for (from_id, to_id) in configurations_map.iter().enumerate() {
                let c1 = &input_all_node_config[from_id];
                let c2 = &output_all_node_config[*to_id];
                let v1 = line_to_counts(c1, 0);
                let v2 = line_to_counts(c2, 0);
                pairs.push((Pairings::new(v1, v2), from_id, *to_id));
            }

            Ok(LabelMapping {
                mapping_problem: &mapping_problem,
                mappings: std::iter::repeat(0..0)
                    .take(0)
                    .multi_cartesian_product()
                    .peekable(),
                pairings: pairs,
                all_good_pairings: vec![],
                hashmaped_good_pairings: vec![
                    Vec::new();
                    mapping_problem.input_all_node_config.len()
                ], //Vec::with_capacity(mapping_problem.input_all_node_config.len()),
            })
        }

        fn get_matrix_matching_from_pairing(pairing: &Vec<Comb>) -> Option<Vec<Vec<usize>>> {
            let mut matrix: Vec<Vec<usize>> = vec![];
            for v in pairing.iter() {
                matrix.push(v.get()?.clone());
            }
            Some(matrix)
        }

        pub fn get_hashmap_version_pairing_matching(
            &self,
            pairing: &(&Vec<Comb>, usize, usize),
        ) -> Result<HashMap<Group, HashSet<Group>>> {
            let matrix = LabelMapping::get_matrix_matching_from_pairing(pairing.0)
                .ok_or(anyhow!("Matrix Creation Failed"))?;

            let mut curr_matching: HashMap<Group, HashSet<Group>> = HashMap::new();

            let from_id = pairing.1;
            let from_line = &self.mapping_problem.input_all_node_config[from_id];
            let to_id = pairing.2;
            let to_line = &self.mapping_problem.output_all_node_config[to_id];

            for (ind_r, row) in matrix.iter().enumerate() {
                let input_group = &from_line.parts[ind_r].group;
                for (ind_e, element) in row.iter().enumerate() {
                    let output_goup = &to_line.parts[ind_e].group;
                    if *element != 0 {
                        curr_matching
                            .entry((*input_group).clone())
                            .or_insert(HashSet::new())
                            .insert((*output_goup).clone());
                    }
                }
            }

            Ok(curr_matching)
        }

        /// This function iterates over the self.pairings variable and saves every resulting matching in hashed versiom to self.hashmaped_good_pairings
        pub fn hashmaped_pairings_filling(&mut self) {
            let mut pairings_clone = self.pairings.clone();

            for _ in pairings_clone.iter_mut().map(|pairing| {
                while let Some(curr_pairing) = pairing.0.next() {
                    let from_id = pairing.1;
                    let hashed_matching = self
                        .get_hashmap_version_pairing_matching(&(curr_pairing, pairing.1, pairing.2))
                        .unwrap();
                    self.hashmaped_good_pairings[from_id].push(hashed_matching);
                }
            }) {}
        }

        /// This function fills up the self.all_good_pairings and self.hasmaped_good_pairings variables with
        /// Every possible pairing for further use
        pub fn all_possible_pairings_test(&mut self) -> Result<()> {
            let mut pairings_clone = self.pairings.clone();

            for _ in pairings_clone.iter_mut().map(|pairing| {
                while let Some(curr_pairing) = pairing.0.next() {
                    self.all_good_pairings.push(
                        LabelMapping::get_matrix_matching_from_pairing(curr_pairing)
                            .ok_or(anyhow!("Pairing matrix creating failed"))
                            .unwrap(),
                    );
                    println!(
                        "Matching matrix for: {}, to: {}, and the matrix is: {:?}",
                        pairing.1,
                        pairing.2,
                        self.all_good_pairings.last().unwrap()
                    );
                    println!(
                        "Hashmaped version of it: {:?}\n\n\n",
                        self.get_hashmap_version_pairing_matching(&(
                            curr_pairing,
                            pairing.1,
                            pairing.2
                        ))
                    );

                    let from_id = pairing.1;
                    let hashed_matching = self
                        .get_hashmap_version_pairing_matching(&(curr_pairing, pairing.1, pairing.2))
                        .unwrap();
                    self.hashmaped_good_pairings[from_id].push(hashed_matching);
                }
            }) {}
            //println!("I am doing something!");
            Ok(())
        }

        /// We wish to test if to_test Hashmap's every element is a subset of containing_map HashMap's every element or not
        pub fn is_hashmap_contained(
            &self,
            to_test: &HashMap<Group, HashSet<Group>>,
            containing_map: &HashMap<Group, HashSet<Group>>,
        ) -> bool {
            for (gr, map_gr) in to_test.iter() {
                let to_compare = containing_map.get(gr).unwrap();
                if !map_gr.is_subset(to_compare) {
                    return false;
                }
            }
            return true;
        }

        /// Currently not the most efficient way of removing for a given input node config the worse mappings
        fn hashed_pairings_reducing_for_config(
            &self,
            from_id: usize,
            label_maps: &Vec<HashMap<Group, HashSet<Group>>>,
        ) -> Vec<HashMap<Group, HashSet<Group>>> {
            let mut keep: Vec<bool> = vec![true; self.hashmaped_good_pairings[from_id].len()];
            for (check_id, maping) in self.hashmaped_good_pairings[from_id].iter().enumerate() {
                for (to_compare_id, maping_comp) in
                    self.hashmaped_good_pairings[from_id].iter().enumerate()
                {
                    if check_id != to_compare_id && keep[to_compare_id] == true {
                        if self.is_hashmap_contained(maping, maping_comp) {
                            keep[to_compare_id] = false;
                        }
                    }
                }
            }

            let mut new_maps = Vec::new();

            for (ind, v) in keep.iter().enumerate() {
                if *v {
                    new_maps.push(label_maps[ind].clone());
                }
            }

            return new_maps;
        }

        /// For every input node configuration we wish to throw out label_maps that contain even just one other label_map
        pub fn hashed_pairings_reducing(&mut self) {
            let mut new_hashmaping =
                vec![Vec::new(); self.mapping_problem.input_all_node_config.len()];
            for (from_id, label_maps) in self.hashmaped_good_pairings.iter().enumerate() {
                new_hashmaping[from_id] =
                    self.hashed_pairings_reducing_for_config(from_id, label_maps);
            }
            self.hashmaped_good_pairings = new_hashmaping;
        }

        ///For every input node config calculate how many possible mappings are left in the current
        /// Configuations mapping and create a Cartesian product on which we can iterate over
        pub fn cartesian_choices_hashed(&self) -> MultiProduct<Range<usize>> {
            let cartesian: Vec<usize> = self
                .hashmaped_good_pairings
                .iter()
                .map(|v| v.len()) // Map each element to its length
                .collect(); // Collect the results into a Vec<usize>

            crate::cartesian::cartesian::cartesian_product_ranges(cartesian)
        }

        pub fn all_good_pairings(&self) -> &Vec<Vec<Vec<usize>>> {
            return &self.all_good_pairings;
        }

        pub fn hashmaped_good_pairings(&self) -> &Vec<Vec<HashMap<Group, HashSet<Group>>>> {
            return &self.hashmaped_good_pairings;
        }

        pub fn pairings(&self) -> &Vec<(Pairings, usize, usize)> {
            return &self.pairings;
        }
    }

    impl<'a> Iterator for LabelMapping<'a> {
        type Item = Vec<usize>;

        fn next(&mut self) -> Option<Self::Item> {
            self.mappings.next()
        }
    }

    /// Given two LCl problems (input, output) we whis to find a f:N_in -> N_out
    /// and \forall l \in N_in g_l: l -> f(l) set parition function such that
    /// only allowed edge configurations remain
    #[derive(Debug, Clone)]
    pub struct MappingProblem {
        input_problem: Problem,
        output_problem: Problem,
        //Every possible node configuration for the input problem
        pub input_all_node_config: Vec<Line>,
        //Every possible node configuration for the output problem
        pub output_all_node_config: Vec<Line>,
        configurations_map: ConfigurationsMapping,
    }

    impl MappingProblem {
        pub fn new(in_p: Problem, out_p: Problem) -> MappingProblem {
            let input_all_node_config = in_p.active.all_choices(true);
            let output_all_node_config = out_p.active.all_choices(true);
            let in_p_size = input_all_node_config.len();
            let out_p_size = output_all_node_config.len();
            MappingProblem {
                input_problem: in_p,
                output_problem: out_p,
                input_all_node_config: input_all_node_config,
                output_all_node_config: output_all_node_config,
                configurations_map: ConfigurationsMapping::new(in_p_size, out_p_size),
            }
        }

        /// Just writes out the .all_choices() function results of the input and output problems
        pub fn long_describ_problems(&self) {
            println!(
                "Input active: {:?}",
                self.input_problem.active.all_choices(true)
            );
            let mapping = self
                .input_problem
                .mapping_label_text
                .iter()
                .cloned()
                .collect();
            for v in self.input_problem.active.all_choices(true) {
                println!("{}", v.to_string(&mapping));
            }
            //println!("{:?}", self.input_problem.passive.all_choices(true));

            //println!("{:?}", self.output_problem.active.all_choices(true));
            println!(
                "Output active: {:?}",
                self.output_problem.active.all_choices(true)
            );
            let mapping = self
                .output_problem
                .mapping_label_text
                .iter()
                .cloned()
                .collect();
            for v in self.output_problem.active.all_choices(true) {
                println!("{}", v.to_string(&mapping));
            }
        }

        pub fn print_input_line_config(&self, line: &Line) -> String {
            let mapping = self
                .input_problem
                .mapping_label_text
                .iter()
                .cloned()
                .collect();

            line.to_string(&mapping)
        }

        pub fn print_output_line_config(&self, line: &Line) -> String {
            let mapping = self
                .output_problem
                .mapping_label_text
                .iter()
                .cloned()
                .collect();

            line.to_string(&mapping)
        }

        /// Given the ConfigurationsMapping and LabelMapping it creates for
        /// every input problem label the possible output labels
        fn summarized_labelling() -> HashMap<Group, HashSet<Group>> {
            let mut summarized_labels = HashMap::new();

            summarized_labels
        }

        /// Given a map of the node configs it creates a LabelMapping variable
        pub fn labelmapping_from_the_config(
            &self,
            config_map: &Vec<usize>,
        ) -> Result<LabelMapping> {
            LabelMapping::new(
                &self,
                &self.input_all_node_config,
                &self.output_all_node_config,
                &config_map,
            )
        }

        pub fn next_config(&mut self) -> Option<Vec<usize>> {
            self.configurations_map.next()
        }

        /// A testing function to see what does Pairings do.
        pub fn label_mapping_for_config(&mut self) -> Result<()> {
            while let Some(curr_config) = self.configurations_map.next() {
                let mut label_map = self.labelmapping_from_the_config(&curr_config)?;
                println!("Current configurations mapping: {:?}", curr_config);
                //label_map.good_labeling_in_pairing();
                label_map.all_possible_pairings_test()?;
                println!(
                    "All possible pairings in matrix form for this configuration mapping: {:?}",
                    label_map.all_good_pairings()
                );
                println!(
                    "All possible pairings in hashmaped form: {:?}",
                    label_map.hashmaped_good_pairings()
                );
                //break;
            }

            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {

    use itertools::Itertools;
    use permutator::CartesianProductIterator;
    use std::collections::{HashMap, HashSet};
    use streaming_iterator::StreamingIterator;

    use super::{
        mapping_problem::{ConfigurationsMapping, MappingProblem},
        *,
    };
    use round_eliminator_lib::{
        group::Group,
        problem::{self, Problem},
    };

    #[test]
    fn cartesian_prod() {
        let mut multi_prod = (0..3)
            .map(|i| (i * 2)..(i * 2 + 2))
            .multi_cartesian_product();
        assert_eq!(multi_prod.next(), Some(vec![0, 2, 4]));
        assert_eq!(multi_prod.next(), Some(vec![0, 2, 5]));
        assert_eq!(multi_prod.next(), Some(vec![0, 3, 4]));
        assert_eq!(multi_prod.next(), Some(vec![0, 3, 5]));
        assert_eq!(multi_prod.next(), Some(vec![1, 2, 4]));
        assert_eq!(multi_prod.next(), Some(vec![1, 2, 5]));
        assert_eq!(multi_prod.next(), Some(vec![1, 3, 4]));
        assert_eq!(multi_prod.next(), Some(vec![1, 3, 5]));
        assert_eq!(multi_prod.next(), None);

        for v in (0..3).map(|i| (i * 2)..(i * 2 + 2)) {
            println!("Val: {:?}", v);
        }
    }

    #[test]
    fn cartesian_changing_size() {
        let test = ConfigurationsMapping::new(3, 2);
        for v in test {
            println!("Current mapping: {:?}", v);
        }
    }

    #[test]
    fn varying_cartesian_product() {
        let n: usize = 5;
        let bm: Vec<&[usize]> = vec![&[0, 1, 2]; n];
        let test: CartesianProductIterator<usize> = CartesianProductIterator::new(&bm);
        for cr in CartesianProductIterator::new(&bm) {
            println!("{:?}", cr);
        }
    }

    #[test]
    fn problems_long_describ() {
        let mut test = MappingProblem::new(
            Problem::from_string("A A AX Y \nB B BY A\n\nAB CD").unwrap(),
            Problem::from_string("A B B D\nC D D A\n\nAB CD").unwrap(),
        );
        test.long_describ_problems();

        test.label_mapping_for_config().unwrap();
    }

    #[test]
    fn all_pairings_listing() {
        let mut test = MappingProblem::new(
            Problem::from_string("A A AX Y \nB B BY A\n\nAB CD").unwrap(),
            Problem::from_string("A B B D\nC D D A\n\nAB CD").unwrap(),
        );
    }

    #[test]
    fn hasmapping_from_pairing() {
        let mut test = MappingProblem::new(
            Problem::from_string("A A AX Y \nB B BY A\n\nAB CD").unwrap(),
            Problem::from_string("A B B D\nC D D A\n\nAB CD").unwrap(),
        );
        test.long_describ_problems();

        let curr_config = test.next_config().unwrap();
        println!("Current config mapping: {:?}", curr_config);
        let label_map = test.labelmapping_from_the_config(&curr_config).unwrap();
        let mut current_pairing = label_map.pairings();
        let mut one_pairing = current_pairing[0].clone();
        println!(
            "Mapping from input line: {:?} to output line: {:?} with line describ {:?} to {:?}",
            test.print_input_line_config(&test.input_all_node_config[one_pairing.1]),
            test.print_output_line_config(&test.output_all_node_config[one_pairing.2]),
            test.input_all_node_config[one_pairing.1],
            test.output_all_node_config[one_pairing.2]
        );

        let true_asnwers: Vec<HashMap<Group, HashSet<Group>>> = vec![
            HashMap::from([
                (
                    Group(vec![0]),
                    HashSet::from([Group(vec![2]), Group(vec![1])]),
                ),
                (Group(vec![2]), HashSet::from([Group(vec![0])])),
            ]),
            HashMap::from([
                (
                    Group(vec![0]),
                    HashSet::from([Group(vec![0]), Group(vec![1])]),
                ),
                (Group(vec![2]), HashSet::from([Group(vec![2])])),
            ]),
            HashMap::from([
                (
                    Group(vec![0]),
                    HashSet::from([Group(vec![0]), Group(vec![1]), Group(vec![2])]),
                ),
                (Group(vec![2]), HashSet::from([Group(vec![1])])),
            ]),
        ];
        let mut func_res = Vec::new();
        while let Some(v) = one_pairing.0.next() {
            func_res.push(
                label_map
                    .get_hashmap_version_pairing_matching(&(v, one_pairing.1, one_pairing.2))
                    .unwrap(),
            );
            println!("Current hashed mapping: {:?}", func_res.last().unwrap());
        }

        assert_eq!(true_asnwers, func_res);
    }

    #[test]
    fn hashmap_containment() {
        let mut test = MappingProblem::new(
            Problem::from_string("A A AX Y \nB B BY A\n\nAB CD").unwrap(),
            Problem::from_string("A B B D\nC D D A\n\nAB CD").unwrap(),
        );
        test.long_describ_problems();
        let curr_config = test.next_config().unwrap();
        println!("Current config mapping: {:?}", curr_config);
        let mut label_map = test.labelmapping_from_the_config(&curr_config).unwrap();

        label_map.hashmaped_pairings_filling();
        let two_hasmaps = vec![
            HashMap::from([
                (
                    Group(vec![0]),
                    HashSet::from([Group(vec![2]), Group(vec![0])]),
                ),
                (Group(vec![2]), HashSet::from([Group(vec![0])])),
            ]),
            HashMap::from([
                (
                    Group(vec![0]),
                    HashSet::from([Group(vec![2]), Group(vec![1]), Group(vec![0])]),
                ),
                (Group(vec![2]), HashSet::from([Group(vec![0])])),
            ]),
        ];
        println!(
            "Are these two hashmaps contained in each other? Small: {:?}, Big: {:?}",
            two_hasmaps[0], two_hasmaps[1]
        );
        assert!(label_map.is_hashmap_contained(&two_hasmaps[0], &two_hasmaps[1]));
    }

    #[test]
    fn hasmaps_reduction() {
        let mut test = MappingProblem::new(
            Problem::from_string("A A AX Y Y\n\nAB CD").unwrap(),
            Problem::from_string("A B B D A\n\nAB CD").unwrap(),
        );
        test.long_describ_problems();
        let curr_config = test.next_config().unwrap();
        println!("Current config mapping: {:?}", curr_config);
        let mut label_map = test.labelmapping_from_the_config(&curr_config).unwrap();

        let removed = HashMap::from([
            (
                Group(vec![0]),
                HashSet::from([Group(vec![2]), Group(vec![1]), Group(vec![0])]),
            ),
            (
                Group(vec![2]),
                HashSet::from([Group(vec![0]), Group(vec![1])]),
            ),
        ]);

        label_map.hashmaped_pairings_filling();
        println!(
            "Every hashmapping for every node configuration: {:?}",
            label_map.hashmaped_good_pairings()[0]
        );
        assert!(label_map.hashmaped_good_pairings()[0].contains(&removed));
        label_map.hashed_pairings_reducing();
        println!(
            "Every hashmapping for every node configuration: {:?}",
            label_map.hashmaped_good_pairings()[0]
        );
        assert!(!label_map.hashmaped_good_pairings()[0].contains(&removed));
    }

    #[test]
    fn iterate_cartesians() {
        let mut test = MappingProblem::new(
            Problem::from_string("A A AX Y Y\n\nAB CD").unwrap(),
            Problem::from_string("A B B D A\n\nAB CD").unwrap(),
        );
        test.long_describ_problems();
        let curr_config = test.next_config().unwrap();
        println!("Current config mapping: {:?}", curr_config);
        let mut label_map = test.labelmapping_from_the_config(&curr_config).unwrap();

        let removed = HashMap::from([
            (
                Group(vec![0]),
                HashSet::from([Group(vec![2]), Group(vec![1]), Group(vec![0])]),
            ),
            (
                Group(vec![2]),
                HashSet::from([Group(vec![0]), Group(vec![1])]),
            ),
        ]);

        label_map.hashmaped_pairings_filling();
        println!(
            "Every hashmapping for every node configuration: {:?}",
            label_map.hashmaped_good_pairings()[0]
        );
        assert!(label_map.hashmaped_good_pairings()[0].contains(&removed));
        label_map.hashed_pairings_reducing();
        println!(
            "Every hashmapping for every node configuration: {:?}",
            label_map.hashmaped_good_pairings()[0]
        );
        assert!(!label_map.hashmaped_good_pairings()[0].contains(&removed));

        println!("\n\n");
        for (indi, v) in label_map.hashmaped_good_pairings().iter().enumerate() {
            println!(
                "The indi: {:?}, have the following hasmaps: {:?}, have the size of {:?}",
                indi,
                v,
                v.len()
            );
        }

        let mut all_maps_combinations = label_map.cartesian_choices_hashed();
        for i in 0..4 {
            for j in 0..10 {
                assert_eq!(all_maps_combinations.next(), Some(vec![i, j]));
            }
        }
    }

    #[test]
    fn iterate_cartesians_1def_2coloring() {
        let mut test = MappingProblem::new(
            Problem::from_string("A A A\nA A X\nB B B\nB B Y\n\nA B\nA Y\nX B\nX Y\nX X\nX Y\nY Y").unwrap(),
            Problem::from_string("A A X\nB B Y\n\nA B\nA A\nA Y\nB X\nB B\nX B\nY A\nX Y").unwrap(),
        );
        test.long_describ_problems();
        let curr_config = test.next_config().unwrap();
        println!("Current config mapping: {:?}", curr_config);
        let mut label_map = test.labelmapping_from_the_config(&curr_config).unwrap();

       
        label_map.hashmaped_pairings_filling();
        println!(
            "Every hashmapping for every node configuration: {:?}",
            label_map.hashmaped_good_pairings()[0]
        );
        label_map.hashed_pairings_reducing();
        println!(
            "Every hashmapping for every node configuration: {:?}",
            label_map.hashmaped_good_pairings()[0]
        );

        println!("\n\n");
        for (indi, v) in label_map.hashmaped_good_pairings().iter().enumerate() {
            println!(
                "The indi: {:?}, have the following hasmaps: {:?}, have the size of {:?}",
                indi,
                v,
                v.len()
            );
        }

        let mut all_maps_combinations = label_map.cartesian_choices_hashed();
        for i in 0..4 {
            for j in 0..10 {
                //assert_eq!(all_maps_combinations.next(), Some(vec![i, j]));
            }
        }
    }
}
