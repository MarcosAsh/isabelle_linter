//! What the core and a prover's server say to each other, one JSON object per line.
//! Offsets are bytes into the file as it is on disk.

use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Range {
    pub start: usize,
    pub stop: usize,
}

impl Range {
    pub fn contains(&self, other: &Range) -> bool {
        self.start <= other.start && other.stop <= self.stop
    }
}

/// Replace `range` of the file with `text`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edit {
    pub range: Range,
    pub text: String,
}

/// Something `unused` might delete. Its range may be wider than its text.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Piece {
    pub kind: String,
    pub text: String,
    pub range: Range,
    pub line: usize,
}

/// A proof step that closes its goal, like Isabelle's `by` or a terminal tactic.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Step {
    pub text: String,
    pub range: Range,
    pub line: usize,
}

/// A theorem with its proof. `ok` is false if it did not check as written.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Decl {
    pub key: String,
    pub name: String,
    pub range: Range,
    pub line: usize,
    pub ok: bool,
    #[serde(default)]
    pub steps: Vec<Step>,
    #[serde(default)]
    pub pieces: Vec<Piece>,
}

/// What a prover's server knows that the core does not.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Hello {
    pub prover: String,
    pub version: String,
    /// Methods `faster_step` tries in place of a step.
    #[serde(default)]
    pub closers: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "do", rename_all = "snake_case")]
pub enum Ask {
    /// Check the declaration again with the edits applied, from the state before it.
    Run { edits: Vec<Edit> },
    /// Run `text` on the goal of step number `step` in place of that step.
    Step { step: usize, text: String },
}

/// A serial question is asked alone, so that other questions do not distort its times.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Question {
    pub key: String,
    pub decl: String,
    #[serde(flatten)]
    pub ask: Ask,
    pub timeout_ms: u64,
    pub runs: u32,
    #[serde(default)]
    pub serial: bool,
}

/// `ms` has one time per run, of the edited declaration or step alone.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Answer {
    pub key: String,
    pub verdict: String,
    #[serde(default)]
    pub ms: Vec<u64>,
    #[serde(default)]
    pub message: String,
}

impl Answer {
    pub fn unanswered(key: &str) -> Answer {
        Answer {
            key: key.to_string(),
            verdict: "unanswered".to_string(),
            ms: Vec::new(),
            message: String::new(),
        }
    }

    pub fn closes(&self) -> bool {
        self.verdict == "closes"
    }

    pub fn median_ms(&self) -> u64 {
        let mut ms = self.ms.clone();
        ms.sort();
        ms.get(ms.len() / 2).copied().unwrap_or(0)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "request", rename_all = "snake_case")]
pub enum Request {
    Hello,
    Load { file: String },
    Ask { question: Question },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "response", rename_all = "snake_case")]
pub enum Response {
    Hello { hello: Hello },
    Loaded { decls: Vec<Decl> },
    Answer { answer: Answer },
    Error { message: String },
}
