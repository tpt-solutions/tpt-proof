//! A cache of solver results for verification conditions.
//!
//! A VC is identified by its encoded SMT-LIB script and the solver timeout, hashed
//! with FNV-1a, which is stable across runs and toolchains. Only deterministic results
//! are stored: `unsat` and counterexamples. Timeouts, unknowns, and errors are never
//! cached, since a later run may answer differently.
//!
//! The cache is in memory, or in a directory with one file per entry. A failure to
//! write a cache file never changes a verdict: the result is simply not kept.

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use crate::smt::{check, encode, parse_output, SolverConfig};
use crate::vc::Vc;
use crate::Outcome;

/// Caches solver results. See the module documentation.
#[derive(Debug, Default)]
pub struct VcCache {
    directory: Option<PathBuf>,
    memory: HashMap<u64, String>,
    hits: usize,
}

impl VcCache {
    /// A cache that lives only as long as this value.
    pub fn in_memory() -> VcCache {
        VcCache::default()
    }

    /// A cache stored in `directory`, which is created if it does not exist.
    pub fn in_directory(directory: impl Into<PathBuf>) -> std::io::Result<VcCache> {
        let directory = directory.into();
        fs::create_dir_all(&directory)?;
        Ok(VcCache {
            directory: Some(directory),
            memory: HashMap::new(),
            hits: 0,
        })
    }

    /// How many checks were answered from the cache.
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Checks `vc`, answering from the cache when the same VC was checked before.
    pub fn check(&mut self, vc: &Vc, config: &SolverConfig) -> Outcome {
        let script = match encode(vc) {
            Ok(script) => script,
            Err(err) => return Outcome::Error(err.to_string()),
        };
        let key = fnv1a(format!("timeout {}\n{script}", config.timeout_ms).as_bytes());
        if let Some(raw) = self.lookup(key) {
            self.hits += 1;
            return parse_output(&raw);
        }
        let outcome = check(vc, config);
        let raw = match &outcome {
            Outcome::SolverUnsat => Some("unsat\n".to_string()),
            Outcome::Failed { counterexample } => Some(format!("sat\n{counterexample}\n")),
            _ => None,
        };
        if let Some(raw) = raw {
            self.store(key, raw);
        }
        outcome
    }

    fn lookup(&self, key: u64) -> Option<String> {
        if let Some(raw) = self.memory.get(&key) {
            return Some(raw.clone());
        }
        let directory = self.directory.as_ref()?;
        fs::read_to_string(directory.join(format!("{key:016x}"))).ok()
    }

    fn store(&mut self, key: u64, raw: String) {
        if let Some(directory) = &self.directory {
            // A write failure only means the result is not kept for next time.
            let _ = fs::write(directory.join(format!("{key:016x}")), &raw);
        }
        self.memory.insert(key, raw);
    }
}

/// FNV-1a, 64 bit. Stable across runs, unlike the standard library's hashers.
pub fn fnv1a(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc::{Expr, Sort};
    use std::path::PathBuf;

    fn vc() -> Vc {
        Vc {
            name: "cached".to_string(),
            vars: vec![("x".to_string(), Sort::Int)],
            assumptions: vec![Expr::Le(
                Box::new(Expr::Int(0)),
                Box::new(Expr::Var("x".into())),
            )],
            goal: Expr::Le(Box::new(Expr::Int(0)), Box::new(Expr::Var("x".into()))),
        }
    }

    /// A solver path that does not exist, so any answer must come from the cache.
    fn no_solver() -> SolverConfig {
        SolverConfig {
            z3: PathBuf::from("definitely-not-a-real-z3-binary"),
            timeout_ms: 1_000,
        }
    }

    #[test]
    fn a_stored_result_answers_without_the_solver() {
        let mut cache = VcCache::in_memory();
        let vc = vc();
        let key = fnv1a(
            format!(
                "timeout {}\n{}",
                no_solver().timeout_ms,
                encode(&vc).expect("encodes")
            )
            .as_bytes(),
        );
        cache.memory.insert(key, "unsat\n".to_string());
        assert_eq!(cache.check(&vc, &no_solver()), Outcome::SolverUnsat);
        assert_eq!(cache.hits(), 1);
    }

    #[test]
    fn a_missing_solver_is_an_error_and_is_not_cached() {
        let mut cache = VcCache::in_memory();
        let vc = vc();
        assert!(matches!(cache.check(&vc, &no_solver()), Outcome::Error(_)));
        assert!(cache.memory.is_empty());
        assert_eq!(cache.hits(), 0);
    }

    #[test]
    fn a_different_timeout_is_a_different_entry() {
        let mut cache = VcCache::in_memory();
        let vc = vc();
        let key = fnv1a(format!("timeout {}\n{}", 1_000, encode(&vc).expect("encodes")).as_bytes());
        cache.memory.insert(key, "unsat\n".to_string());
        let other = SolverConfig {
            timeout_ms: 2_000,
            ..no_solver()
        };
        assert!(matches!(cache.check(&vc, &other), Outcome::Error(_)));
    }

    #[test]
    fn fnv1a_matches_the_published_value_for_a_known_input() {
        // FNV-1a of the empty input is the offset basis.
        assert_eq!(fnv1a(b""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(fnv1a(b"a"), 0xaf63_dc4c_8601_ec8c);
    }
}
