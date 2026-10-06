//! `similarity --corpora DIR`: runs the gate over the fetched corpora
//! (`scripts/check_similarity.sh` fetches them) and exits nonzero on any
//! unwaived match. Configuration is in `provenance/similarity/`:
//! - `corpora.tsv`: the implementations compared against, pinned;
//! - `scope.tsv`: the library files that are fully specified (base code, not
//!   scanned) or not library code (not scanned). Every other `.rs` file under
//!   `crates/morphiq-numerics/src` is scanned, except tests and generated files;
//! - `waivers.tsv`: matches reviewed and accepted, by fingerprint.

use morphiq_numerics_similarity::{Base, Corpus, Language, Match, matches, tokenize};
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const LIBRARY: &str = "crates/morphiq-numerics/src";
const CONFIG: &str = "provenance/similarity";

/// The fields of each non-comment, non-blank line of a tab-separated file.
fn records(path: &str) -> Vec<Vec<String>> {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    text.lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| l.split('\t').map(str::to_owned).collect())
        .collect()
}

/// Every file under `dir`, recursively, skipping `.git`.
fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.file_name().is_some_and(|n| n == ".git") {
            continue;
        }
        if path.is_dir() {
            walk(&path, out);
        } else {
            out.push(path);
        }
    }
}

fn relative(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

/// Generated files carry the generators' header on their first line.
fn generated(text: &str) -> bool {
    text.lines()
        .next()
        .is_some_and(|l| l.contains("written by `generators/"))
}

fn test_file(path: &str) -> bool {
    path.ends_with("/tests.rs") || path.contains("/tests/")
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let Some(corpora_dir) = args
        .iter()
        .position(|a| a == "--corpora")
        .and_then(|i| args.get(i + 1))
    else {
        eprintln!("usage: similarity --corpora DIR");
        return ExitCode::from(2);
    };

    // Scope: base code and exclusions, each named file required to exist.
    let mut base = Base::default();
    base.add_canonical_forms();
    let mut not_scanned: HashSet<String> = HashSet::new();
    for r in records(&format!("{CONFIG}/scope.tsv")) {
        let (kind, path) = (r[0].as_str(), r[1].clone());
        let text =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("scope.tsv names {path}: {e}"));
        match kind {
            "fully-specified" => base.add(&tokenize(&text, Language::Rust)),
            "excluded" => {}
            _ => panic!("scope.tsv: unknown kind {kind}"),
        }
        not_scanned.insert(path);
    }
    let mut ours = Vec::new();
    let mut files = Vec::new();
    walk(Path::new(LIBRARY), &mut files);
    for path in files {
        let name = relative(&path);
        if Language::of_path(&name) != Some(Language::Rust)
            || test_file(&name)
            || not_scanned.contains(&name)
        {
            continue;
        }
        let text = fs::read_to_string(&path).unwrap();
        if generated(&text) {
            continue;
        }
        ours.push((name, tokenize(&text, Language::Rust)));
    }
    println!(
        "scanned: {}",
        if ours.is_empty() {
            "none".to_owned()
        } else {
            ours.iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        }
    );

    // Corpora: every C, C++ or Rust file under each fetched corpus.
    let mut corpus = Corpus::default();
    for r in records(&format!("{CONFIG}/corpora.tsv")) {
        let name = &r[0];
        let root = Path::new(corpora_dir).join(name);
        let mut files = Vec::new();
        walk(&root, &mut files);
        let before = corpus.len();
        for path in files {
            let shown = relative(path.strip_prefix(&root).unwrap());
            let Some(language) = Language::of_path(&shown) else {
                continue;
            };
            let Ok(bytes) = fs::read(&path) else { continue };
            corpus.add(
                name,
                &shown,
                tokenize(&String::from_utf8_lossy(&bytes), language),
            );
        }
        let count = corpus.len() - before;
        if count == 0 {
            eprintln!(
                "corpus {name}: no source files under {}; was it fetched?",
                root.display()
            );
            return ExitCode::from(2);
        }
        println!("corpus {name}: {count} files");
    }

    // Matches, less the waived.
    let waived: HashSet<(String, String)> = records(&format!("{CONFIG}/waivers.tsv"))
        .into_iter()
        .map(|r| (r[0].clone(), r[1].clone()))
        .collect();
    let mut failed = false;
    for (name, tokens) in &ours {
        for m in matches(name, tokens, &corpus, &base) {
            let key = (format!("{:016x}", m.fingerprint), m.corpus.clone());
            if waived.contains(&key) {
                println!("waived: {}", m.report());
            } else {
                report(&m);
                failed = true;
            }
        }
    }
    if failed {
        eprintln!(
            "similarity: matches above; review each, then fix the code or waive it in {CONFIG}/waivers.tsv"
        );
        return ExitCode::FAILURE;
    }
    println!("similarity: OK");
    ExitCode::SUCCESS
}

fn report(m: &Match) {
    println!("match: {}", m.report());
}
