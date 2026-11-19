//! A lint asks questions in rounds, with all answers so far, until it asks nothing new; then it
//! turns the answers into findings.

use crate::protocol::{Answer, Decl, Edit, File};
use std::collections::HashMap;

pub type Answers = HashMap<String, Answer>;

#[derive(Clone, Debug)]
pub struct Options {
    /// Time limit of one question, in ms.
    pub timeout_ms: u64,
    /// An edited declaration gets this many times the time of the declaration as written.
    pub factor: f64,
    /// Questions sent to the prover at once.
    pub batch: usize,
    /// Runs when a fix is timed against the declaration as written.
    pub runs: u32,
    /// Questions `unused` asks ahead per declaration while it goes through pieces one by one.
    pub unused_ahead: usize,
    /// `faster_step` leaves steps under this many ms alone.
    pub faster_step_slow_ms: u64,
    /// How many times faster a step's replacement has to be.
    pub faster_step_speedup: f64,
    /// `simp_hygiene` reports a rule once the file's proofs try it this often.
    pub simp_hygiene_min: u64,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            timeout_ms: 30_000,
            factor: 3.0,
            batch: 500,
            runs: 3,
            unused_ahead: 4,
            faster_step_slow_ms: 1000,
            faster_step_speedup: 2.0,
            simp_hygiene_min: 100,
        }
    }
}

impl Options {
    pub fn set(&mut self, assignment: &str) -> Result<(), String> {
        let (name, value) = assignment
            .split_once('=')
            .ok_or(format!("expected NAME=VALUE, got {assignment}"))?;
        let bad = |_| format!("bad value for {name}: {value}");
        match name {
            "timeout_ms" => self.timeout_ms = value.parse().map_err(bad)?,
            "factor" => {
                self.factor = value
                    .parse()
                    .map_err(|_| format!("bad value for {name}: {value}"))?
            }
            "batch" => self.batch = value.parse().map_err(bad)?,
            "runs" => self.runs = value.parse().map_err(bad)?,
            "unused_ahead" => self.unused_ahead = value.parse().map_err(bad)?,
            "faster_step_slow_ms" => self.faster_step_slow_ms = value.parse().map_err(bad)?,
            "faster_step_speedup" => {
                self.faster_step_speedup = value
                    .parse()
                    .map_err(|_| format!("bad value for {name}: {value}"))?
            }
            "simp_hygiene_min" => self.simp_hygiene_min = value.parse().map_err(bad)?,
            _ => return Err(format!("unknown option {name}")),
        }
        Ok(())
    }

    /// Below a second, timing noise alone could make an edited declaration run out of time.
    pub fn budget_ms(&self, original: &Answer) -> u64 {
        ((original.median_ms() as f64 * self.factor) as u64)
            .max(1000)
            .min(self.timeout_ms)
    }
}

/// The edits are the fix, each checked by the prover.
#[derive(Clone, Debug, PartialEq)]
pub struct Finding {
    pub lint: String,
    pub decl: String,
    pub line: usize,
    pub message: String,
    pub edits: Vec<Edit>,
}

pub trait Lint {
    fn name(&self) -> &'static str;
    fn ask(
        &self,
        decls: &[Decl],
        answers: &Answers,
        options: &Options,
    ) -> Vec<crate::protocol::Question>;
    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding>;
    /// What the loaded file shows without any question.
    fn read(&self, _file: &File) -> Vec<Finding> {
        Vec::new()
    }
}
