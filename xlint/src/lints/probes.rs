//! Theorems whose hypotheses contradict each other, and predicates that hold for every input or
//! for none. Automation can miss these, so they are only reported.

use crate::lint::{Answers, Finding, Lint, Options};
use crate::protocol::{Ask, Decl, Question};

/// Core tactics only, so that a project without Mathlib still parses them.
const AUTOMATION: &str =
    "(intros; first | contradiction | decide | omega | (simp_all; done) | grind)";

fn question(decl: &Decl, claim: &str, options: &Options) -> Question {
    Question {
        key: format!("{}:probe:{claim}", decl.key),
        decl: decl.key.clone(),
        ask: Ask::Probe {
            claim: claim.to_string(),
            tactic: AUTOMATION.to_string(),
        },
        timeout_ms: options.probe_ms,
        runs: 1,
        serial: false,
    }
}

fn ask(decls: &[Decl], claims: &[&str], answers: &Answers, options: &Options) -> Vec<Question> {
    decls
        .iter()
        .filter(|d| d.ok)
        .flat_map(|d| {
            claims
                .iter()
                .filter(|c| d.probes.iter().any(|p| p == *c))
                .map(move |c| (d, c))
        })
        .map(|(d, c)| question(d, c, options))
        .filter(|q| !answers.contains_key(&q.key))
        .collect()
}

/// The claims of `decl` that automation proved.
fn proved<'a>(
    decl: &Decl,
    claims: &[&'a str],
    answers: &Answers,
    options: &Options,
) -> Vec<&'a str> {
    claims
        .iter()
        .filter(|c| {
            let key = question(decl, c, options).key;
            answers.get(&key).is_some_and(|a| a.closes())
        })
        .copied()
        .collect()
}

fn finding(lint: &str, decl: &Decl, message: String) -> Finding {
    Finding {
        lint: lint.to_string(),
        decl: decl.key.clone(),
        line: decl.line,
        message,
        edits: Vec::new(),
    }
}

pub struct Vacuous;

impl Lint for Vacuous {
    fn name(&self) -> &'static str {
        "vacuous"
    }

    fn ask(
        &self,
        decls: &[Decl],
        answers: &Answers,
        options: &Options,
    ) -> Vec<crate::protocol::Question> {
        ask(decls, &["vacuous"], answers, options)
    }

    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding> {
        decls
            .iter()
            .filter(|d| !proved(d, &["vacuous"], answers, options).is_empty())
            .map(|d| {
                let message = format!("the hypotheses of `{}` contradict each other: `{AUTOMATION}` proves False from them", d.name);
                finding(self.name(), d, message)
            })
            .collect()
    }
}

pub struct Constant;

impl Lint for Constant {
    fn name(&self) -> &'static str {
        "constant"
    }

    fn ask(
        &self,
        decls: &[Decl],
        answers: &Answers,
        options: &Options,
    ) -> Vec<crate::protocol::Question> {
        ask(decls, &["always", "never"], answers, options)
    }

    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding> {
        decls
            .iter()
            .filter_map(|d| {
                let which = match proved(d, &["always", "never"], answers, options)[..] {
                    ["always"] => "every input",
                    ["never"] => "no input",
                    _ => return None,
                };
                let message = format!("`{}` holds for {which}: `{AUTOMATION}` proves it", d.name);
                Some(finding(self.name(), d, message))
            })
            .collect()
    }
}
