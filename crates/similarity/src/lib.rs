//! The similarity gate (`docs/PROVENANCE.md`, "Similarity gate"): the library's
//! design-choice source compared, token by token, against the implementations
//! the policy lists.
//!
//! **Method.** Winnowing (S. Schleimer, D. S. Wilkerson, A. Aiken, "Winnowing:
//! local algorithms for document fingerprinting", SIGMOD 2003), the algorithm
//! behind MOSS and Dolos, over normalized tokens:
//! - comments, strings, preprocessor lines and attributes are dropped, and so
//!   are declaration and type words, which a translation between C and Rust
//!   changes anyway;
//! - every identifier becomes `I` and every number `N`, so renaming doesn't hide
//!   a copy.
//!
//! A k-gram is `K` consecutive normalized tokens. The corpus keeps the minimum
//! hash in every window of `W` k-grams; our files keep every k-gram. So any
//! shared run of at least `W + K − 1` tokens is found, and none shorter than `K`
//! is reported. `K = 23` and `W = 17` are Dolos's documented defaults
//! (<https://dolos.ugent.be/docs/running.html>), validated there and not tuned
//! on this code.
//!
//! **Base code.** Shared mathematics produces shared token runs: every Horner
//! evaluation normalizes alike. K-grams that also occur in base code are not
//! matched:
//! - the library's fully specified modules, which the policy allows to state a
//!   published algorithm operation by operation;
//! - the canonical Horner forms (Knuth, *TAOCP* vol. 2, §4.6.4), generated here.
//!
//! A match is seeded only by a non-base k-gram, then extended to the full
//! shared run.
//!
//! **Nothing foreign is printed.** A match is reported by our file and lines,
//! the run's length, its fingerprint, and the corpus and path it matched in.
//! The policy forbids giving a model the listed source, and a report may be
//! read by one.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

/// The k-gram length, in normalized tokens.
pub const K: usize = 23;
/// The winnowing window, in k-grams.
pub const W: usize = 17;

/// A normalized token and the source line it starts on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    /// The normalized token's hash (FNV-1a of its text).
    pub hash: u64,
    /// 1-based line.
    pub line: u32,
}

/// The source language, which decides comments, attributes and literals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Language {
    /// C and C++, preprocessor lines included.
    C,
    /// Rust, nested comments, attributes and lifetimes included.
    Rust,
}

impl Language {
    /// From a file extension: `.rs` is Rust; the C and C++ extensions are C.
    #[must_use]
    pub fn of_path(path: &str) -> Option<Self> {
        let ext = path.rsplit_once('.').map(|(_, e)| e)?;
        match ext {
            "rs" => Some(Self::Rust),
            "c" | "h" | "cc" | "cpp" | "cxx" | "hpp" | "hh" | "hxx" | "ipp" | "inl" | "tcc" => {
                Some(Self::C)
            }
            _ => None,
        }
    }
}

/// FNV-1a, 64-bit, over bytes.
fn fnv(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// Words that a translation between C and Rust adds, drops or changes:
/// declarations, qualifiers and types.
const DROPPED: &[&str] = &[
    "let",
    "mut",
    "pub",
    "const",
    "static",
    "fn",
    "struct",
    "impl",
    "use",
    "mod",
    "crate",
    "self",
    "Self",
    "super",
    "as",
    "where",
    "unsafe",
    "extern",
    "inline",
    "typedef",
    "volatile",
    "register",
    "auto",
    "signed",
    "unsigned",
    "int",
    "long",
    "short",
    "char",
    "float",
    "double",
    "void",
    "bool",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "usize",
    "isize",
    "f32",
    "f64",
    "uint8_t",
    "uint16_t",
    "uint32_t",
    "uint64_t",
    "int8_t",
    "int16_t",
    "int32_t",
    "int64_t",
    "size_t",
    "constexpr",
    "noexcept",
    "template",
    "typename",
    "namespace",
    "class",
    "private",
    "public",
    "protected",
    "virtual",
    "override",
    "friend",
    "restrict",
    "__restrict",
    "_Bool",
    "attribute_hidden",
    "static_assert",
];

/// Control words kept as themselves.
const KEPT: &[&str] = &[
    "if", "else", "for", "while", "do", "return", "break", "continue", "loop", "match", "switch",
    "case", "default", "goto",
];

/// Operators, longest first, for maximal munch.
const OPERATORS: &[&str] = &[
    ">>=", "<<=", "...", "..=", "::", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=",
    "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "++", "--", "..",
];

/// Punctuation dropped as type or path syntax: `:` and `::` (type ascription,
/// paths), `->` (return types).
const DROPPED_PUNCTUATION: &[&str] = &[":", "::", "->"];

/// The normalized tokens of `source`.
#[must_use]
pub fn tokenize(source: &str, language: Language) -> Vec<Token> {
    let b = source.as_bytes();
    let (mut i, mut line, mut at_line_start) = (0usize, 1u32, true);
    let mut out = Vec::new();
    let emit = |out: &mut Vec<Token>, text: &str, line: u32| {
        out.push(Token {
            hash: fnv(text.as_bytes()),
            line,
        });
    };
    while i < b.len() {
        let c = b[i];
        if c == b'\n' {
            line += 1;
            at_line_start = true;
            i += 1;
            continue;
        }
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // Comments.
        if c == b'/' && b.get(i + 1) == Some(&b'/') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if c == b'/' && b.get(i + 1) == Some(&b'*') {
            let mut depth = 1;
            i += 2;
            while i < b.len() && depth > 0 {
                if b[i] == b'\n' {
                    line += 1;
                }
                if language == Language::Rust && b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
                    depth += 1;
                    i += 2;
                } else if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        // Preprocessor lines (C) and attributes (Rust).
        if c == b'#' {
            if language == Language::C && at_line_start {
                while i < b.len() && b[i] != b'\n' {
                    if b[i] == b'\\' && b.get(i + 1) == Some(&b'\n') {
                        line += 1;
                        i += 1;
                    }
                    i += 1;
                }
                continue;
            }
            if language == Language::Rust {
                let mut j = i + 1;
                if b.get(j) == Some(&b'!') {
                    j += 1;
                }
                if b.get(j) == Some(&b'[') {
                    let mut depth = 0;
                    while j < b.len() {
                        match b[j] {
                            b'[' => depth += 1,
                            b']' => {
                                depth -= 1;
                                if depth == 0 {
                                    j += 1;
                                    break;
                                }
                            }
                            b'\n' => line += 1,
                            _ => {}
                        }
                        j += 1;
                    }
                    i = j;
                    continue;
                }
            }
        }
        at_line_start = false;
        // Strings, including Rust raw strings.
        if c == b'"'
            || (language == Language::Rust
                && c == b'r'
                && matches!(b.get(i + 1), Some(b'"' | b'#')))
        {
            let start_line = line;
            if c == b'r' {
                let mut hashes = 0;
                i += 1;
                while b.get(i) == Some(&b'#') {
                    hashes += 1;
                    i += 1;
                }
                if b.get(i) != Some(&b'"') {
                    // `r#ident`, a raw identifier.
                    emit(&mut out, "I", line);
                    while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                        i += 1;
                    }
                    continue;
                }
                i += 1;
                loop {
                    if i >= b.len() {
                        break;
                    }
                    if b[i] == b'\n' {
                        line += 1;
                    }
                    if b[i] == b'"' && (0..hashes).all(|h| b.get(i + 1 + h) == Some(&b'#')) {
                        i += 1 + hashes;
                        break;
                    }
                    i += 1;
                }
            } else {
                i += 1;
                while i < b.len() && b[i] != b'"' {
                    if b[i] == b'\\' {
                        i += 1;
                    }
                    if b.get(i) == Some(&b'\n') {
                        line += 1;
                    }
                    i += 1;
                }
                i += 1;
            }
            emit(&mut out, "S", start_line);
            continue;
        }
        // Character literals, and Rust lifetimes (dropped).
        if c == b'\'' {
            let close = if b.get(i + 1) == Some(&b'\\') {
                (i + 2..b.len().min(i + 12)).find(|&j| b[j] == b'\'')
            } else if b.get(i + 2) == Some(&b'\'') {
                Some(i + 2)
            } else {
                None
            };
            if let Some(end) = close {
                emit(&mut out, "S", line);
                i = end + 1;
            } else {
                i += 1;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
            }
            continue;
        }
        // Numbers: digits, hexadecimal, exponents, suffixes.
        if c.is_ascii_digit() || (c == b'.' && b.get(i + 1).is_some_and(u8::is_ascii_digit)) {
            let hex = c == b'0' && matches!(b.get(i + 1), Some(b'x' | b'X'));
            i += 1;
            while i < b.len() {
                let d = b[i];
                let previous = b[i - 1].to_ascii_lowercase();
                let exponent_sign =
                    matches!(d, b'+' | b'-') && (previous == b'p' || (!hex && previous == b'e'));
                if d.is_ascii_alphanumeric()
                    || d == b'_'
                    || exponent_sign
                    || (d == b'.' && b.get(i + 1) != Some(&b'.'))
                {
                    i += 1;
                } else {
                    break;
                }
            }
            emit(&mut out, "N", line);
            continue;
        }
        // Identifiers and words.
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            let word = &source[start..i];
            if DROPPED.contains(&word) {
                continue;
            }
            if KEPT.contains(&word) {
                emit(&mut out, word, line);
            } else {
                emit(&mut out, "I", line);
            }
            continue;
        }
        // Operators and punctuation.
        let op = OPERATORS
            .iter()
            .find(|op| b[i..].starts_with(op.as_bytes()))
            .map_or_else(|| &source[i..=i], |op| *op);
        i += op.len().max(1);
        if !op.is_ascii() || DROPPED_PUNCTUATION.contains(&op) {
            continue;
        }
        emit(&mut out, op, line);
    }
    out
}

/// The polynomial base of the rolling k-gram hash (odd).
const BASE: u64 = 0x9e37_79b9_7f4a_7c15;

/// The hash of every k-gram, in order: `hashes[i]` covers tokens `i..i + K`.
#[must_use]
pub fn kgrams(tokens: &[Token]) -> Vec<u64> {
    if tokens.len() < K {
        return Vec::new();
    }
    let top = (1..K).fold(1u64, |p, _| p.wrapping_mul(BASE));
    let mut h = tokens[..K]
        .iter()
        .fold(0u64, |h, t| h.wrapping_mul(BASE).wrapping_add(t.hash));
    let mut out = Vec::with_capacity(tokens.len() - K + 1);
    out.push(h);
    for i in K..tokens.len() {
        h = h
            .wrapping_sub(tokens[i - K].hash.wrapping_mul(top))
            .wrapping_mul(BASE)
            .wrapping_add(tokens[i].hash);
        out.push(h);
    }
    out
}

/// Winnowing: the positions of the minimum hash in every window of `W`
/// k-grams, the rightmost on ties, each position once.
#[must_use]
pub fn winnow(hashes: &[u64]) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    if hashes.is_empty() {
        return out;
    }
    let windows = hashes.len().saturating_sub(W) + 1;
    for start in 0..windows {
        let end = (start + W).min(hashes.len());
        let mut best = start;
        for i in start..end {
            if hashes[i] <= hashes[best] {
                best = i;
            }
        }
        if out.last() != Some(&best) {
            out.push(best);
        }
    }
    out
}

/// The canonical Horner forms, normalized, as base code: the statement form
/// `t = c + x·t` and the nested form `c + x·(c + x·(…))`, with identifier or
/// literal coefficients, up to degree 24.
#[must_use]
pub fn canonical_forms() -> Vec<String> {
    let mut forms = Vec::new();
    for coefficient in ["I", "N"] {
        for n in 1..=24 {
            let mut s = String::new();
            for _ in 0..n {
                let _ = write!(s, "I = {coefficient} + I * I ; ");
            }
            forms.push(s.clone());
            let mut s = String::new();
            for _ in 0..n {
                let _ = write!(s, "I = I * I + {coefficient} ; ");
            }
            forms.push(s);
            let mut nested = String::new();
            for _ in 0..n {
                let _ = write!(nested, "{coefficient} + I * ( ");
            }
            nested.push_str(coefficient);
            for _ in 0..n {
                nested.push_str(" )");
            }
            forms.push(nested);
        }
    }
    forms
}

/// The tokens of a space-separated normalized form.
fn form_tokens(form: &str) -> Vec<Token> {
    form.split_whitespace()
        .map(|t| Token {
            hash: fnv(t.as_bytes()),
            line: 0,
        })
        .collect()
}

/// Corpus fingerprints: winnowed k-gram hashes, with where they occur.
#[derive(Default)]
pub struct Corpus {
    files: Vec<(String, String, Vec<Token>)>,
    index: HashMap<u64, Vec<(usize, usize)>>,
}

impl Corpus {
    /// Adds a file of corpus `name` at `path`, tokenized.
    pub fn add(&mut self, name: &str, path: &str, tokens: Vec<Token>) {
        let file = self.files.len();
        let hashes = kgrams(&tokens);
        for position in winnow(&hashes) {
            self.index
                .entry(hashes[position])
                .or_default()
                .push((file, position));
        }
        self.files.push((name.to_owned(), path.to_owned(), tokens));
    }

    /// The number of files.
    #[must_use]
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Whether no file was added.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
}

/// K-gram hashes of base code, never matched.
#[derive(Default)]
pub struct Base(HashSet<u64>);

impl Base {
    /// Adds every k-gram of `tokens`.
    pub fn add(&mut self, tokens: &[Token]) {
        self.0.extend(kgrams(tokens));
    }

    /// Adds the canonical forms.
    pub fn add_canonical_forms(&mut self) {
        for form in canonical_forms() {
            self.add(&form_tokens(&form));
        }
    }
}

/// A shared run between one of our files and a corpus file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Match {
    /// Our file.
    pub file: String,
    /// The run's first and last lines in our file.
    pub lines: (u32, u32),
    /// The run's length in normalized tokens.
    pub tokens: usize,
    /// The run's fingerprint: a hash of its normalized tokens, for waivers.
    pub fingerprint: u64,
    /// The corpus and the path within it.
    pub corpus: String,
    /// The path within the corpus.
    pub path: String,
}

/// Every maximal shared run between `ours` and the corpus seeded by a
/// non-base k-gram, longest first; one per region of our file and corpus file.
#[must_use]
pub fn matches(file: &str, ours: &[Token], corpus: &Corpus, base: &Base) -> Vec<Match> {
    let hashes = kgrams(ours);
    let mut found: Vec<Match> = Vec::new();
    let mut covered: HashSet<(usize, usize)> = HashSet::new(); // (corpus file, our start)
    for (i, h) in hashes.iter().enumerate() {
        if base.0.contains(h) {
            continue;
        }
        let Some(hits) = corpus.index.get(h) else {
            continue;
        };
        for &(f, j) in hits {
            let theirs = &corpus.files[f].2;
            // Hashes can collide: confirm the k-gram, then extend both ways.
            if (0..K).any(|d| ours[i + d].hash != theirs[j + d].hash) {
                continue;
            }
            let (mut a, mut c) = (i, j);
            while a > 0 && c > 0 && ours[a - 1].hash == theirs[c - 1].hash {
                a -= 1;
                c -= 1;
            }
            let mut len = K;
            while a + len < ours.len()
                && c + len < theirs.len()
                && ours[a + len].hash == theirs[c + len].hash
            {
                len += 1;
            }
            if !covered.insert((f, a)) {
                continue;
            }
            let fingerprint = ours[a..a + len]
                .iter()
                .fold(0u64, |acc, t| acc.wrapping_mul(BASE).wrapping_add(t.hash));
            found.push(Match {
                file: file.to_owned(),
                lines: (ours[a].line, ours[a + len - 1].line),
                tokens: len,
                fingerprint,
                corpus: corpus.files[f].0.clone(),
                path: corpus.files[f].1.clone(),
            });
        }
    }
    found.sort_by(|x, y| y.tokens.cmp(&x.tokens).then(x.lines.cmp(&y.lines)));
    found
}

impl Match {
    /// The report line: our side only, and where the run matched.
    #[must_use]
    pub fn report(&self) -> String {
        format!(
            "{}:{}-{}  {} tokens  fingerprint {:016x}  matches {}:{}",
            self.file,
            self.lines.0,
            self.lines.1,
            self.tokens,
            self.fingerprint,
            self.corpus,
            self.path
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(tokens: &[Token]) -> Vec<u64> {
        tokens.iter().map(|t| t.hash).collect()
    }

    #[test]
    fn c_and_rust_spellings_of_one_computation_normalize_alike() {
        let c = "static double f(double x, double y) {\n  /* c */ double t = x * y + 0x1.8p-3; // tail\n  return t - y;\n}";
        let rust = "#[inline]\nfn f(x: f64, y: f64) -> f64 {\n    let t = x * y + 0.1875; /* a /* nested */ comment */\n    return t - y;\n}";
        assert_eq!(
            text(&tokenize(c, Language::C)),
            text(&tokenize(rust, Language::Rust))
        );
    }

    #[test]
    fn comments_strings_preprocessor_and_lifetimes_leave_no_tokens() {
        let c = "#define A(x) \\\n  ((x) + 1)\n/* x + y */ // z\n\"a + b\"";
        assert_eq!(
            text(&tokenize(c, Language::C)),
            text(&tokenize("\"\"", Language::C))
        );
        let rust = "#![allow(x)]\nfn f<'a>(x: &'a str) -> char { 'z' }";
        let plain = "f<>(x: & str) { 'q' }";
        assert_eq!(
            text(&tokenize(rust, Language::Rust)),
            text(&tokenize(plain, Language::Rust))
        );
    }

    #[test]
    fn numbers_lex_whole() {
        for n in [
            "1",
            "1.5e-3",
            "0x1.fp+2",
            "1e+10f",
            "123_456u64",
            "0x7ff0_0000_0000_0000",
            ".5",
        ] {
            assert_eq!(tokenize(n, Language::Rust).len(), 1, "{n}");
        }
        assert_eq!(tokenize("0..10", Language::Rust).len(), 3);
    }

    /// A pseudo-random token stream from a seed (xorshift), over `alphabet`
    /// symbols.
    fn stream(seed: u64, n: usize, alphabet: u64) -> Vec<Token> {
        let mut s = seed;
        (0..n)
            .map(|i| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                Token {
                    hash: fnv(&(s % alphabet).to_le_bytes()),
                    line: u32::try_from(i).unwrap() + 1,
                }
            })
            .collect()
    }

    /// Winnowing's guarantee: a shared run of `W + K − 1` tokens is always
    /// found; one of `K − 1` never is.
    #[test]
    fn shared_runs_are_found_from_the_guarantee_length_and_never_below_k() {
        for seed in 1..200u64 {
            let shared = stream(seed * 7919, W + K - 1, 1 << 20);
            let mut ours = stream(seed, 300, 1 << 20);
            let mut theirs = stream(seed + 1_000_000, 500, 1 << 20);
            ours.splice(100..100, shared.iter().copied());
            theirs.splice(250..250, shared.iter().copied());
            let mut corpus = Corpus::default();
            corpus.add("c", "p", theirs.clone());
            let found = matches("ours", &ours, &corpus, &Base::default());
            assert!(found.iter().any(|m| m.tokens >= W + K - 1), "seed {seed}");

            let short = &shared[..K - 1];
            let mut ours = stream(seed + 5, 300, 1 << 20);
            let mut theirs = stream(seed + 6, 500, 1 << 20);
            ours.splice(50..50, short.iter().copied());
            theirs.splice(60..60, short.iter().copied());
            let mut corpus = Corpus::default();
            corpus.add("c", "p", theirs);
            assert!(
                matches("ours", &ours, &corpus, &Base::default()).is_empty(),
                "seed {seed}"
            );
        }
    }

    #[test]
    fn base_code_seeds_no_match_but_a_longer_copy_still_matches() {
        let horner: String = (0..12).map(|_| "t = c + x * t;\n").collect();
        let ours = tokenize(&format!("fn f() {{ {horner} }}"), Language::Rust);
        let mut corpus = Corpus::default();
        corpus.add(
            "c",
            "p",
            tokenize(&format!("double g() {{ {horner} }}"), Language::C),
        );
        let mut base = Base::default();
        base.add_canonical_forms();
        assert!(
            matches("ours", &ours, &corpus, &base).is_empty(),
            "Horner is shared mathematics"
        );
        assert!(!matches("ours", &ours, &corpus, &Base::default()).is_empty());

        // A distinctive sequence next to it still seeds a match.
        let distinctive =
            "if (a > b) { s = a - b; r = s / (q + 1); } else { while (k < n) { k += m[k]; } }";
        let ours = tokenize(
            &format!("fn f() {{ {horner} {distinctive} }}"),
            Language::Rust,
        );
        let mut corpus = Corpus::default();
        corpus.add(
            "c",
            "p",
            tokenize(
                &format!("void g() {{ {horner} {distinctive} }}"),
                Language::C,
            ),
        );
        let found = matches("ours", &ours, &corpus, &base);
        assert!(found.iter().any(|m| m.tokens >= K), "{found:?}");
    }

    #[test]
    fn a_report_carries_no_corpus_text() {
        let body = "if (zqxv_secret > 1) { zqxv_secret = zqxv_secret * 3 + 0x1.2345p-7; return zqxv_secret - 2; } else { return zqxv_secret / 5 + 7; }";
        let ours = tokenize(&format!("fn f() {{ {body} }}"), Language::Rust);
        let mut corpus = Corpus::default();
        corpus.add(
            "lib",
            "src/e.c",
            tokenize(
                &format!("double g() {{ {body} }} /* zqxv_comment */"),
                Language::C,
            ),
        );
        let found = matches("ours.rs", &ours, &corpus, &Base::default());
        assert!(!found.is_empty());
        for m in found {
            let line = m.report();
            assert!(
                !line.contains("zqxv") && !line.contains("0x1.2345"),
                "{line}"
            );
            assert!(
                line.starts_with("ours.rs:") && line.contains("matches lib:src/e.c"),
                "{line}"
            );
        }
    }
}
