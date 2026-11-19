//! Rules the simplifier keeps trying for nothing. Nothing is checked again without them, so the
//! findings only inform.

use crate::lint::{Answers, Finding, Lint, Options};
use crate::protocol::{Ask, Decl, Question};
use std::collections::BTreeMap;

pub struct SimpHygiene;

/// A rule that rewrites in at most this share of its tries is reported too.
const USED_SHARE: f64 = 0.1;

#[derive(Default)]
struct Total<'a> {
    tried: u64,
    used: u64,
    /// The declarations that tried it, with their tries.
    users: Vec<(&'a Decl, u64)>,
}

fn theorems(decls: &[Decl]) -> impl Iterator<Item = &Decl> {
    decls.iter().filter(|d| d.ok && d.kind == "theorem")
}

fn question(decl: &Decl, options: &Options) -> Question {
    Question {
        key: format!("{}:stats", decl.key),
        decl: decl.key.clone(),
        ask: Ask::Stats,
        timeout_ms: options.timeout_ms,
        runs: 1,
        serial: false,
    }
}

/// `Namespace.name` is the rule of a declaration written as `name`.
fn declares(decl: &Decl, rule: &str) -> bool {
    !decl.name.is_empty()
        && rule
            .strip_suffix(decl.name.as_str())
            .is_some_and(|namespace| namespace.is_empty() || namespace.ends_with('.'))
}

impl Lint for SimpHygiene {
    fn name(&self) -> &'static str {
        "simp_hygiene"
    }

    fn ask(&self, decls: &[Decl], _answers: &Answers, options: &Options) -> Vec<Question> {
        theorems(decls).map(|d| question(d, options)).collect()
    }

    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding> {
        let mut totals: BTreeMap<&str, Total> = BTreeMap::new();
        let mut counted = 0;
        for decl in theorems(decls) {
            let Some(answer) = answers.get(&question(decl, options).key) else {
                continue;
            };
            if !answer.closes() {
                continue;
            }
            counted += 1;
            for rule in &answer.rules {
                let total = totals.entry(&rule.name).or_default();
                total.tried += rule.tried;
                total.used += rule.used;
                total.users.push((decl, rule.tried));
            }
        }
        let note = format!(
            "information only, nothing was checked again without it; counted over {counted} of {} theorems",
            theorems(decls).count()
        );
        let mut reported: Vec<(&str, Total)> = totals
            .into_iter()
            .filter(|(_, t)| {
                t.tried >= options.simp_hygiene_min && t.used as f64 <= USED_SHARE * t.tried as f64
            })
            .collect();
        reported.sort_by_key(|(name, t)| (std::cmp::Reverse(t.tried), *name));
        reported
            .into_iter()
            .map(|(rule, total)| {
                let declared = decls.iter().find(|d| declares(d, rule));
                let most = total.users.iter().max_by_key(|(_, tried)| *tried);
                let at = declared.or(most.map(|(d, _)| *d));
                let rewrote = match total.used {
                    0 => "never rewrote".to_string(),
                    n => format!("rewrote {n} times"),
                };
                let advice = match declared {
                    Some(_) => "declared here: drop its simp attribute, or `simp [-rule]` where it is not needed",
                    None => "imported: `attribute [-simp]` in this file, or `simp [-rule]` in its steps",
                };
                Finding {
                    lint: self.name().to_string(),
                    decl: at.map(|d| d.key.clone()).unwrap_or_default(),
                    line: at.map(|d| d.line).unwrap_or(1),
                    message: format!(
                        "simp rule `{rule}` tried {} times in {} theorems, {rewrote}\n  {advice}\n  {note}",
                        total.tried,
                        total.users.len()
                    ),
                    edits: Vec::new(),
                }
            })
            .collect()
    }
}
