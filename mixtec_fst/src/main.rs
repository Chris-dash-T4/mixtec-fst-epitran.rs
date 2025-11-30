mod rewrite;

use parserule::rulefst::{sigma_star, weighted_sigma_star};
use rustfst::utils::transducer;
use parserule::{rulefst, ruleparse};
use rustfst::prelude::concat::concat;
use rustfst::prelude::determinize::{determinize_with_config, DeterminizeConfig, DeterminizeType};
use rustfst::prelude::rm_epsilon::rm_epsilon;
use rustfst::Semiring;
use std::collections::HashMap;
use std::{fs::File, path::Path, sync::Arc};
use std::io::prelude::*;
use std::cmp::Ordering;

use clap::Parser;
use itertools::{enumerate, Itertools};
use rustfst::{prelude::{compose::compose, minimize_with_config, tr_sort, union::union, Fst, ILabelCompare, MinimizeConfig, MutableFst, OLabelCompare, SerializableFst, TropicalWeight, VectorFst}, DrawingConfig, SymbolTable};
use parserule::normalize::nfd_normalize;

use crate::rewrite::{compile_as_linear};

#[derive(Parser)]
struct Args {
    /// Path to write the FST to
    outpath: String,
    /// Path to load the FST from
    #[arg(short,long)]
    load: Option<String>,
    /// Test file (CSV)
    #[arg(short,long)]
    test: Option<String>,
    /// Linearize G3
    #[arg(long)]
    linearize: bool,
    /// Is test input G3
    #[arg(long)]
    g3: bool,
    /// Output OpenFST-style text file
    #[arg(long)]
    openfst: Option<String>,
    /// Source directory
    #[arg(long)]
    srcdir: Option<String>,
    /// No minimization
    #[arg(long)]
    no_min: bool,
}

#[derive(Debug, serde::Deserialize)]
struct Entry {
    form: String,
    segmentation: String,
    //lx_neg: String,
    //lx_comto: String,
}

pub fn apply_fst_to_output_string(
    symt: Arc<SymbolTable>,
    mut fst: VectorFst<TropicalWeight>,
    output: String,
) -> anyhow::Result<VectorFst<TropicalWeight>> {
    let symt: Arc<SymbolTable> = symt.clone();
    let mut acc = rulefst::string_to_linear_automaton(symt, &output);
    acc.set_symts_from_fst(&fst);
    // println!("acc={:?}", acc);
    // println!("fst={:?}", fst);

    tr_sort(&mut fst, OLabelCompare {});
    tr_sort(&mut acc, ILabelCompare {});

    let composed_fst: VectorFst<TropicalWeight> = compose(fst, acc)?;
    // println!("composed_fst={:?}", composed_fst);

    Ok(composed_fst)
}

fn can_generate_form(fst: &VectorFst<TropicalWeight>, input: &str, form: &str, is_g3: bool, save_dot: Option<&Path>) -> Result<bool, Box<dyn std::error::Error>> {
    let input = "#".to_string() + input + "#";
    let output = "#".to_string() + form + "#";
    let mut e2e = rulefst::apply_fst_to_string(fst.input_symbols().unwrap().clone(), fst.clone(), input).unwrap();
    minimize_with_config(&mut e2e, MinimizeConfig::default().with_allow_nondet(true))?;
    let paths_all = rulefst::decode_paths_through_fst(fst.input_symbols().unwrap().clone(), e2e.clone());
    let mut seen = HashMap::new();
    for (weight, result) in paths_all {
        match seen.get(&result) {
            Some(&w) => {
                if w > weight {
                    seen.insert(result.clone(), weight);
                }
            }
            None => {
                seen.insert(result.clone(), weight);
            }
            
        }
    }
    for (result, weight) in seen.iter().sorted_by(|(_, w1), (_, w2)| w1.value().partial_cmp(&w2.value()).unwrap_or(Ordering::Equal)) {
        println!("result={}, weight={}", result, weight);
    }
    /*
     */
    let mut generated = if is_g3 {
        apply_fst_to_output_string(fst.output_symbols().unwrap().clone(), e2e, output)?
    } else {
        let get_base = get_fst_g3_to_base(fst.output_symbols().unwrap().clone())?;
        let gen_output = apply_fst_to_output_string(fst.output_symbols().unwrap().clone(), get_base, output)?;
        tr_sort(&mut e2e, OLabelCompare {});
        compose(e2e, gen_output)?
    };
    minimize_with_config(&mut generated, MinimizeConfig::default().with_allow_nondet(true))?;
    if let Some(path) = save_dot { generated.clone().draw(path, &DrawingConfig::default())?; }
    let paths = rulefst::decode_paths_through_fst(fst.output_symbols().unwrap().clone(), generated);
    if let Some((_, result)) = paths.first() {
        println!("result={}", result);
        Ok(result == &("#".to_string() + form + "#"))
    }
    else {
        println!("No result");
        Ok(false)
    }
}

fn get_symt_from_file(path: &str) -> anyhow::Result<Arc<SymbolTable>> {
    let data = std::fs::read_to_string(path)?.to_lowercase();
    let syms = data.split_terminator('\n').map(|c| nfd_normalize(c)).collect::<Vec<_>>(); // Add the super-final state symbol

    let mut symt_inner = SymbolTable::new();
    symt_inner.add_symbols(syms);
    symt_inner.add_symbol("#");
    println!("symt={:?}", symt_inner);
    let symt = Arc::new(symt_inner);
    Ok(symt)
}

fn get_fst_g3_to_base(symt: Arc<SymbolTable>) -> anyhow::Result<VectorFst<TropicalWeight>> {
    let raw_script = r"\>[1234\>]*} -> 0 / {[1234]* _ 
{ -> 0 / _ [1234]+";
    let (_, (script, _what)) = ruleparse::parse_script(
        raw_script
    )?;
    //println!("script={:?}", script);
    let mut fst = rulefst::compile_script(symt.clone(),script.clone())?;
    tr_sort(&mut fst, ILabelCompare {});
    Ok(fst)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    // Import script from file
    let symt = get_symt_from_file("chars.txt")?;
    if args.linearize {
        let raw_script = std::fs::read_to_string("rules/to_linear_base.txt")?;
        let (_, (script, _)) = ruleparse::parse_script(
            raw_script.as_str()
        ).unwrap_or_else(|_| panic!("Failed to parse script"));
        let mut _fst= compile_as_linear(symt.clone(), script)?;
        /*
        let mut fsts = Vec::new();
        for i in 1..5usize {
            let raw_script = std::fs::read_to_string(format!("rules/to_linear_{}.txt",i))?;
            let (_, (script, _)) = ruleparse::parse_script(
                raw_script.as_str()
            ).unwrap_or_else(|_| panic!("Failed to parse script"));
            let mut fst= compile_as_linear(symt.clone(), script)?;
            // These ones actually should be deterministic
            //fst = determinize_with_config(&fst, DeterminizeConfig { delta: 1e-7, det_type: DeterminizeType::DeterminizeDisambiguate })?;
            if i == 1 { tr_sort(&mut fst, OLabelCompare {}); }
            else { tr_sort(&mut fst, ILabelCompare {}); }
            if let Some(path_output) = &args.openfst { fst.write_text(Path::new(path_output).join(format!("linear_{}.fst",i)))?; }
            fsts.push(fst);
        }
        println!("Composing...");
        let mut composed_fst: VectorFst<TropicalWeight> = compose(fsts[0].clone(), fsts[1].clone())?;
        println!("Composition 1/3 complete");
        minimize_with_config(&mut composed_fst, MinimizeConfig { delta: 1e-7, allow_nondet: true })?;
        tr_sort(&mut composed_fst, OLabelCompare {});
        println!("Composing...");
        composed_fst = compose(composed_fst, fsts[2].clone())?;
        println!("Composition 2/3 complete");
        minimize_with_config(&mut composed_fst, MinimizeConfig { delta: 1e-7, allow_nondet: true })?;
        tr_sort(&mut composed_fst, OLabelCompare {});
        println!("Composing...");
        composed_fst = compose(composed_fst, fsts[3].clone())?;
        println!("Composition 3/3 complete");
        composed_fst.write(args.outpath.clone())?;
         */
        return Ok(());
    }


    let mut fst = if let Some(load) = args.load {
        VectorFst::<TropicalWeight>::read(load)?
    } else if let Some(src) = args.srcdir {
        /*
        let sigmastar = sigma_star(symt.clone())?;
        let sigmastar_5xweight = sort_and_compose(
            &sort_and_compose(
                        &sigmastar,
                        &sort_and_compose(
                            &sigmastar,
                            &sigmastar
                        )?
                    )?,
            &sort_and_compose(
                &sigmastar,
                &sigmastar
            )? 
        )?;
         */
        let mut fst = weighted_sigma_star(symt.clone(), 10.0)?;//sort_and_compose(&sigmastar_5xweight, &sigmastar_5xweight)?;
        let mut num_compose = 1;
        for file in std::fs::read_dir(src)? {
            let filepath = file?.path();
            println!("\nProcessing file: {}", filepath.clone().display());
            let raw_script = std::fs::read_to_string(filepath)?;
            let (_, (script, _)) = ruleparse::parse_script(
                raw_script.as_str()
            ).unwrap_or_else(|_| panic!("Failed to parse script"));
            let mut num_rules = 0;
            for (i, rule) in enumerate(script.clone()) {
                println!("Rule {}: {:?}", i+1, rule);
                if let ruleparse::Statement::Rule(_) = rule {
                    num_rules += 1;
                }
            }
            let mut fst_oth = rulefst::compile_script(symt.clone(),script.clone())?;
            if num_rules > num_compose {
                println!("Reweighting...");
                while num_compose < num_rules {
                    concat::<TropicalWeight, VectorFst<_>, VectorFst<_>>(
                        &mut fst,
                        &rustfst::fst![0 => 0; 10.0]
                    )?;
                    num_compose += 1;
                    
                }
            } else {
                for _ in 0..num_compose-num_rules {
                    concat::<TropicalWeight, VectorFst<_>, VectorFst<_>>(
                        &mut fst_oth,
                        &rustfst::fst![0 => 0; 10.0]
                    )?;
                }
            }
            // */
            println!("Unioning...");
            union(&mut fst, &fst_oth)?;
        }
        rm_epsilon(&mut fst)?;
        fst.write(args.outpath.clone())?;
        fst
    } else {
        let raw_script = std::fs::read_to_string("rules/from_14.txt")?;
        let (_, (script, _what)) = ruleparse::parse_script(
            raw_script.as_str()
        ).unwrap_or_else(|_| panic!("Failed to parse script"));
        for (i, rule) in enumerate(script.clone()) {
            println!("Rule {}: {:?}", i+1, rule);
        }
        let mut fst = rulefst::compile_script(symt.clone(),script.clone())?;

        let raw_script = std::fs::read_to_string("rules/from_4.txt")?;
        let (_, (script, _what)) = ruleparse::parse_script(
            raw_script.as_str()
        ).unwrap_or_else(|_| panic!("Failed to parse script"));
        for (i, rule) in enumerate(script.clone()) {
            println!("Rule {}: {:?}", i+1, rule);
        }
        let fst_4 = rulefst::compile_script(symt.clone(),script.clone())?;

        let raw_script = std::fs::read_to_string("rules/special.txt")?;
        let (_, (script, _what)) = ruleparse::parse_script(
            raw_script.as_str()
        ).unwrap_or_else(|_| panic!("Failed to parse script"));
        for (i, rule) in enumerate(script.clone()) {
            println!("Rule {}: {:?}", i+1, rule);
        }
        let fst_oth = rulefst::compile_script(symt.clone(),script.clone())?;
        println!("Unioning...");
        union(&mut fst, &fst_4)?;
        union(&mut fst, &fst_oth)?;
        fst.write(args.outpath.clone())?;
        fst
    };
    if let Some(path_output) = &args.openfst {
        fst.write_text(Path::new(path_output).join("fst_segmentation_notminimized.fst")).expect("That didn't work");
    }
    if !args.no_min {
        println!("Minimizing...");
        minimize_with_config(&mut fst, MinimizeConfig { delta: 1e-7, allow_nondet: true })?;
        println!("Done!");
        fst.write(args.outpath)?;
        if let Some(path_output) = &args.openfst { fst.write_text(Path::new(path_output).join("fst_segmentation.fst"))?; }
    }
    /*
    let e2e = rulefst::apply_fst_to_string(symt.clone(), fst.clone(), "#".to_string() + input.as_str() + "#").unwrap();
    e2e.clone().draw("path_output", &DrawingConfig::default())?;
    let paths = rulefst::decode_paths_through_fst(symt.clone(), e2e);
    let mut seen : HashSet<String> = HashSet::new();
    for (i, (p, s)) in enumerate(paths) {
        if seen.contains(&s) { continue; }
        println!("Path {}: {} -> {}", i, p, s);
        seen.insert(s);
    }
    println!("{} paths found", seen.len());
    // */
    
    let tests = if let Some(testfile) = args.test {
        let mut reader = csv::Reader::from_path(testfile)?; //.unwrap().into_deserialize().collect::<Result<Vec<(String, String)>, _>>()?
        let mut out = Vec::new();
        for r in reader.deserialize() {
            let record : Entry = r?;
            println!("{:?}", record);
            if !record.segmentation.is_empty() { out.push((record.form, record.segmentation.clone())); }
            //if !record.lx_neg.is_empty() { out.push((record.lx_neg, record.lx.clone())); }
        }
        out
    } else { 
        vec![
            ("ni{3>1>4}jo14","ni3jo14##3>1>4##14>14"),
            /*
            ("ni14-", "ni1-"),
            ("chi'14i4", "chi'3i3"),
            ("chi'14i4", "chi'14i4"),
            ("ni4-", "ni1-"),
            ("i4in4", "i3in3"),
            ("i4in4", "i4in4"),
            // */
        ].iter().map(|(x, y)| (x.to_string(), y.to_string())).collect()
    };
    let mut log = File::create("log.txt")?;
    for (input, form) in tests.iter() {
        if can_generate_form(&fst, &input, &form, args.g3, None)? {
            println!("{} -> {} OK", input, form);
        }
        else {
            println!("you get NOTHING. you LOSE. good DAY sir.");
            writeln!(log, "{} -> {} FAILED", input, form)?;
        }
    }
    //[MacroDef(("chars", Group([Disjunction([Group([Char('n')]), Group([Char('i')])]), Char('\n'), Class([Char('1'), Char('2'), Char('3'), Char('4')])])))]
    println!("Hello, world!");
    Ok(())
}
