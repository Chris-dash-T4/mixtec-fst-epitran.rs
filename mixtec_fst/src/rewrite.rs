use std::{collections::HashMap, sync::Arc};
use anyhow::Result;
use itertools::enumerate;
use rustfst::{
    algorithms::concat::concat, fst, prelude::{add_super_final_state, closure::{closure, ClosureType}, compose::compose, determinize::{determinize_with_config, DeterminizeConfig, DeterminizeType}, minimize_with_config, tr_sort, union::union, CoreFst, ExpandedFst, Fst, ILabelCompare, MinimizeConfig, MutableFst, OLabelCompare, StateIterator, TropicalWeight, VectorFst}, utils::{acceptor, transducer}, Semiring, SymbolTable, Tr
};
use colored::Colorize;

use parserule::{ruleparse::{RegexAST, RewriteRule, Statement}, utils::optimize_fst};
use parserule::rulefst::{sigma_star};

pub fn compile_as_linear(symt: Arc<SymbolTable>, script: Vec<Statement>) -> Result<VectorFst<TropicalWeight>> {
    let mut base_fst = sigma_star(symt.clone())?;
    let mut macros: HashMap<String, RegexAST> = HashMap::new();
    for (i,statement) in enumerate(script.clone()) {
        match statement {
            Statement::Comment => (),
            Statement::MacroDef((mac, def)) => {
                macros.insert(mac, def).unwrap_or(RegexAST::Epsilon);
            },
            Statement::Rule(rule) => {
                println!("Processing rule {} of {}: {:?}", i+1, script.len(), rule);
                let mut fst2 = linearze_rule_fst(symt.clone(), &macros, rule.clone(), true)
                    .inspect_err(|e| {
                        println!(
                            "Failed to build rule {:?} having macros {:?}: {}", rule, macros, e
                        )
                    })?;
                optimize_fst(&mut base_fst, 1e-7).unwrap_or(());
                tr_sort(&mut base_fst, OLabelCompare {});
                tr_sort(&mut fst2, ILabelCompare {});
                union(&mut base_fst, &fst2)?;
            }
        }
    }
    println!("Finished processing {} rules", script.len());
    println!("Determinizing...");
    base_fst = determinize_with_config(&base_fst, DeterminizeConfig { delta: 1e-7, det_type: DeterminizeType::DeterminizeFunctional })?;
    println!("Applying segment contexts...");
    let seg_first = node_fst(symt.clone(), &macros, RegexAST::Group(vec![RegexAST::Boundary, RegexAST::Macro("segment".to_string())]))?;
    let tone_seg = node_fst(symt.clone(), &macros, RegexAST::Group(vec![RegexAST::Macro("tone".to_string()), RegexAST::Macro("segment".to_string())]))?;
    let mut fst = sigma_star(symt.clone())?;
    for i in 0..4 {
        let mut fst2 = seg_first.clone();
        // Concatenate i additional segments
        for _ in 0..i {
            concat(&mut fst2, &tone_seg)?;
        }
        concat(&mut fst2, &base_fst)?;
        tr_sort(&mut fst, OLabelCompare {});
        tr_sort(&mut fst2, ILabelCompare {});
        fst = compose(fst, fst2)?;
        println!("Composition {} of 4 complete", i+1);
        println!("Minimizing...");
        optimize_fst(&mut fst, 1e-7).unwrap_or(());
        minimize_with_config(&mut fst, MinimizeConfig { delta: 1e-7, allow_nondet: false })?;
        println!("Minimization complete");
    }

    Ok(fst)
}

pub fn linearze_rule_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    rule: RewriteRule,
    drop_left: bool
) -> Result<VectorFst<TropicalWeight>> {
    
    let mut fst = VectorFst::<TropicalWeight>::new();
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());
    let q0 = fst.add_state();
    fst.set_start(0)?;
    let q1 = fst.add_state();
    fst.set_final(q1, TropicalWeight::one())?;
    fst.emplace_tr(q0, 0, 0, TropicalWeight::one(), q1)?;

    // Compute core (L[{S1>S2}->S1]R##T)
    let underlying_seq = rule.source.clone();
    let underlying_fst = match underlying_seq {
        RegexAST::Group(nodes) => {
            let idx_of_arrow = nodes.iter().position(|x| x == &RegexAST::Char('>'));
            println!("Full sequence: {:?}, index of arrow: {:?}", nodes, idx_of_arrow);
            let new_seq = match idx_of_arrow {
                // Underlying sequence is a process, so we take the part of the sequence before the first arrow
                Some(idx) => nodes[1..idx].to_vec(),
                // Underlying sequence is an unchanged tone, so we take the whole thing
                None => nodes,
            };
            println!("Underlying sequence: {:?}", new_seq);
            input_to_epsilons(node_fst(symt.clone(), macros, RegexAST::Group(new_seq))?)
        }
        _ => panic!("Underlying sequence must be a group")
    };

    let src_fst: VectorFst<TropicalWeight> =
        output_to_epsilons(node_fst(symt.clone(), macros, rule.source)?);
    let tgt_fst: VectorFst<TropicalWeight> =
        input_to_epsilons(node_fst(symt.clone(), macros, rule.target)?);
    let left_fst = match rule.left {
        RegexAST::Epsilon => {
            let mut inner_fst = sigma_star(symt.clone())?;
            closure(&mut inner_fst, ClosureType::ClosureStar);
            inner_fst
        }
        _ => node_fst(symt.clone(), macros, rule.left)?,
    };
    let right_fst = match rule.right {
        RegexAST::Epsilon => {
            let mut inner_fst = sigma_star(symt.clone())?;
            closure(&mut inner_fst, ClosureType::ClosureStar);
            inner_fst
        }
        _ => node_fst(symt.clone(), macros, rule.right)?,
    };
    let univ_acc: VectorFst<TropicalWeight> = sigma_star(symt.clone())?;

    // Ignore left context if requested
    if !drop_left { concat(&mut fst, &left_fst)?; }
    concat(&mut fst, &src_fst)?;
    // Map {L>R} to L in-place
    concat(&mut fst, &underlying_fst)?;
    // Right context and acceptor are kept
    concat(&mut fst, &right_fst)?;
    concat(&mut fst, &univ_acc)?;
    // Output target at the end
    concat(&mut fst, &tgt_fst)?;

    let first_state: u32 = 0;
    let last_state: u32 = (fst.num_states() - 1) as u32;

    //fst.emplace_tr(last_state, 0, 0, 0.0, first_state)?;
    //fst.emplace_tr(first_state, 0, 0, 10.0, last_state)?;
    fst.set_final(last_state, 0.0)?;

    let mut root: VectorFst<TropicalWeight> = fst![0 => 0];//sigma_star(symt.clone())?;

    concat(&mut root, &fst)?;

    root.set_start(0)?;

    optimize_fst(&mut root, 1e-6).unwrap_or(());

    Ok(root)
    /*
    println!("Minimizing...");
    minimize_with_config(&mut root, MinimizeConfig { delta: 1e-7, allow_nondet: true })?;
    println!("Determinizing...");
    determinize_with_config(&root, DeterminizeConfig { delta: 1e-7, det_type: DeterminizeType::DeterminizeNonFunctional })
     */
}

fn node_fst(
    symt: Arc<SymbolTable>,
    macros: &HashMap<String, RegexAST>,
    node: RegexAST,
) -> Result<VectorFst<TropicalWeight>> {
    let mut fst: VectorFst<TropicalWeight> = fst![0 => 0];
    fst.set_input_symbols(symt.clone());
    fst.set_output_symbols(symt.clone());

    match node {
        // Interpret an Epsilon node (leaves `fst` unchanged, since it already includes an epsilon transition).
        RegexAST::Epsilon => (),

        // Interpret a group (a sequence of nodes)
        RegexAST::Group(nodes) => {
            for node2 in nodes {
                let fst2 = node_fst(symt.clone(), macros, node2)?;
                concat(&mut fst, &fst2)?;
            }
        }

        // Interpret a boundary symbol.
        RegexAST::Boundary => {
            let bnd_label = symt.get_label("#").unwrap_or(1);
            let fst2: VectorFst<TropicalWeight> = fst![bnd_label];
            concat(&mut fst, &fst2)?;
        }

        // Interpret a character.
        RegexAST::Char(c) => {
            let label = symt.get_label(c.to_string()).unwrap_or(0);
            let fst2: VectorFst<TropicalWeight> = fst![label => label; 0.0];
            concat(&mut fst, &fst2)?;
        }

        // Interpret a disjunction (a set of mutually-exclusive sequences).
        RegexAST::Disjunction(nodes) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst.add_state();
            let q1 = fst.add_state();
            fst.emplace_tr(q0, 0, 0, TropicalWeight::zero(), q1)?;
            for node in nodes {
                let case_fst = node_fst(symt.clone(), macros, node)?;
                union(&mut fst2, &case_fst)?;
            }
            concat(&mut fst, &fst2)?;
        }

        // Interpret a character class (a set of characters any of which match the expression).
        RegexAST::Class(class) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst2.add_state();
            fst2.set_start(q0)?;
            let q1: u32 = fst2.add_state();
            fst2.set_final(q1, 0.0)?;
            fst2.emplace_tr(q1, 0, 0, TropicalWeight::zero(), q1)?;
            for s in class.iter() {
                let l = symt.get_label(s).unwrap_or_else(|| {
                    eprintln!(
                        "Warning: Symbol '{}' is not in symbol table, using epsilon",
                        s.red()
                    );
                    0
                });
                fst2.emplace_tr(q0, l, l, TropicalWeight::one(), q1)?;
            }
            concat(&mut fst, &fst2)?;
        }

        // Interpret the complement of a character class (a set of characters none of which match the expression).
        RegexAST::ClassComplement(mut class) => {
            let mut fst2: VectorFst<TropicalWeight> = VectorFst::<TropicalWeight>::new();
            let q0 = fst2.add_state();
            fst2.set_start(q0)?;
            let q1: u32 = fst2.add_state();
            fst2.set_final(q1, 0.0)?;
            class.insert("#".to_string());
            class.insert("<eps>".to_string());
            for (l, s) in symt.iter() {
                if !class.contains(s) {
                    fst2.emplace_tr(q0, l, l, TropicalWeight::one(), q1)?;
                }
            }
            concat(&mut fst, &fst2)?;
        }

        // Interpret a Kleene star.
        RegexAST::Star(node) => {
            let mut fst2 = node_fst(symt, macros, *node)?;
            closure(&mut fst2, ClosureType::ClosureStar);
            concat(&mut fst, &fst2)?;
        }

        // Interpret a Kleene plus.
        RegexAST::Plus(node) => {
            let mut fst2 = node_fst(symt, macros, *node)?;
            closure(&mut fst2, ClosureType::ClosurePlus);
            concat(&mut fst, &fst2)?;
        }

        // Interpret an optional node
        RegexAST::Option(node) => {
            let mut fst2: VectorFst<TropicalWeight> = node_fst(symt, macros, *node)?;
            let start_state = fst2.start().unwrap_or_else(|| {
                println!("wFST does not have start state.");
                0
            });
            let final_state = add_super_final_state(&mut fst2);
            fst2.emplace_tr(start_state, 0, 0, 0.0, final_state)
                .unwrap_or_else(|e| println!("{e}: Could not add transition."));
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| println!("{e}: Could not concatenate wFSTs."));
        }

        // Interpret a macro
        RegexAST::Macro(macro_key) => {
            let macro_node = macros.get(&macro_key).unwrap_or_else(|| {
                println!("Macro {macro_key} not defined!");
                &RegexAST::Epsilon
            });
            let fst2 = node_fst(symt, macros, macro_node.clone())?;
            concat(&mut fst, &fst2)
                .unwrap_or_else(|e| println!("{e}: Could not concatenate wFSTs."));
        }

        RegexAST::Comment => (),
    }

    // rm_epsilon(&mut fst).unwrap_or_else(|e| {
    //     eprintln!("Warning: Could not remove epsilon transitions: {}", e);
    // });
    // let mut fst = determinize_with_config(
    //     &fst,
    //     DeterminizeConfig {
    //         delta: 1e-6,
    //         det_type: DeterminizeType::DeterminizeFunctional,
    //     },
    // )?;
    // push_weights(&mut fst, ReweightType::ReweightToInitial)?;
    // minimize_with_config(
    //     &mut fst,
    //     MinimizeConfig {
    //         delta: 1e-7,
    //         allow_nondet: (true),
    //     },
    // )?;

    Ok(fst)
}

fn output_to_epsilons(fst: VectorFst<TropicalWeight>) -> VectorFst<TropicalWeight> {
    let mut fst2 = fst.clone();
    for state in fst2.states_iter() {
        let trs: Vec<Tr<TropicalWeight>> = fst2.pop_trs(state).unwrap_or_default().clone();
        for tr in trs.iter() {
            fst2.emplace_tr(state, tr.ilabel, 0, tr.weight, tr.nextstate)
                .inspect_err(|e| {
                    println!(
                        "{e}: Cannot emplace transition from {state} to {}.",
                        tr.nextstate
                    )
                })
                .unwrap_or(());
        }
    }
    fst2
}

fn input_to_epsilons(fst: VectorFst<TropicalWeight>) -> VectorFst<TropicalWeight> {
    let mut fst2 = fst.clone();
    for state in fst2.states_iter() {
        let trs: Vec<Tr<TropicalWeight>> = fst2.pop_trs(state).unwrap_or_default().clone();
        for tr in trs.iter() {
            fst2.emplace_tr(state, 0, tr.olabel, tr.weight, tr.nextstate)
                .inspect_err(|e| {
                    println!(
                        "{e}: Cannot emplace transition from {state} to {}.",
                        tr.nextstate
                    )
                })
                .unwrap_or(());
        }
    }
    fst2
}