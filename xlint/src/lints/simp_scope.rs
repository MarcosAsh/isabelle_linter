//! Simplifier calls that use the whole simp set in a slow declaration, narrowed to the rules
//! they used if that makes the declaration faster.

use crate::lint::{Answers, Finding, Lint, Options};
use crate::protocol::{Answer, Ask, Decl, Edit, Question};

pub struct SimpScope;

/// The calls to narrow, with the median ms of the declaration as written and with them.
struct Narrowed {
    edits: Vec<(usize, Edit)>,
    before: u64,
    after: u64,
}

struct Search<'a> {
    decl: &'a Decl,
    answers: &'a Answers,
    options: &'a Options,
}

impl Search<'_> {
    fn question(&self, what: &str, ask: Ask, timeout_ms: u64, runs: u32, serial: bool) -> Question {
        Question {
            key: format!("{}:scope:{what}", self.decl.key),
            decl: self.decl.key.clone(),
            ask,
            timeout_ms,
            runs,
            serial,
        }
    }

    fn run(&self, what: &str, edits: &[(usize, Edit)], timeout_ms: u64) -> Question {
        let edits = edits.iter().map(|(_, e)| e.clone()).collect();
        self.question(what, Ask::Run { edits }, timeout_ms, 1, false)
    }

    fn answered(&self, questions: Vec<Question>) -> Result<Vec<&Answer>, Vec<Question>> {
        let (known, missing): (Vec<Question>, Vec<Question>) = questions
            .into_iter()
            .partition(|q| self.answers.contains_key(&q.key));
        if missing.is_empty() {
            Ok(known.iter().map(|q| &self.answers[&q.key]).collect())
        } else {
            Err(missing)
        }
    }

    /// Only a slow declaration is searched.
    fn check(&self) -> Result<Option<Narrowed>, Vec<Question>> {
        if self.decl.simps.is_empty() {
            return Ok(None);
        }
        let original = self.run("original", &[], self.options.timeout_ms);
        let answer = self.answered(vec![original])?[0];
        if !answer.closes() || answer.median_ms() < self.options.simp_scope_slow_ms {
            return Ok(None);
        }
        self.search(self.options.budget_ms(answer))
    }

    /// All narrowed calls at once, else those that work alone, else the fastest of them.
    fn search(&self, budget_ms: u64) -> Result<Option<Narrowed>, Vec<Question>> {
        let calls = 0..self.decl.simps.len();
        let narrow = |call| {
            let ask = Ask::Narrow { call };
            self.question(
                &format!("narrow:{call}"),
                ask,
                self.options.timeout_ms,
                1,
                false,
            )
        };
        let suggested = self.answered(calls.clone().map(narrow).collect())?;
        let edits: Vec<(usize, Edit)> = calls
            .zip(suggested)
            .filter_map(|(call, answer)| {
                let text = answer.suggestions.first()?.clone();
                let range = self.decl.simps[call].range;
                (text != self.decl.simps[call].text).then_some((call, Edit { range, text }))
            })
            .collect();
        if edits.is_empty() {
            return Ok(None);
        }
        let all = self.answered(vec![self.run("all", &edits, budget_ms)])?[0];
        let kept = if all.closes() {
            edits
        } else {
            self.alone(edits, budget_ms)?
        };
        if kept.is_empty() {
            return Ok(None);
        }
        self.time(kept, budget_ms)
    }

    fn alone(
        &self,
        edits: Vec<(usize, Edit)>,
        budget_ms: u64,
    ) -> Result<Vec<(usize, Edit)>, Vec<Question>> {
        let one = |edit: &(usize, Edit)| {
            self.run(
                &format!("one:{}", edit.0),
                std::slice::from_ref(edit),
                budget_ms,
            )
        };
        let answers = self.answered(edits.iter().map(one).collect())?;
        let mut working: Vec<(u64, (usize, Edit))> = edits
            .into_iter()
            .zip(answers)
            .filter(|(_, a)| a.closes())
            .map(|(e, a)| (a.median_ms(), e))
            .collect();
        if working.len() < 2 {
            return Ok(working.into_iter().map(|(_, e)| e).collect());
        }
        let together: Vec<(usize, Edit)> = working.iter().map(|(_, e)| e.clone()).collect();
        if self.answered(vec![self.run("working", &together, budget_ms)])?[0].closes() {
            return Ok(together);
        }
        working.sort_by_key(|(ms, (call, _))| (*ms, *call));
        Ok(working.into_iter().take(1).map(|(_, e)| e).collect())
    }

    fn time(
        &self,
        edits: Vec<(usize, Edit)>,
        budget_ms: u64,
    ) -> Result<Option<Narrowed>, Vec<Question>> {
        let timing = |what: &str, edits: &[(usize, Edit)]| {
            let edits = edits.iter().map(|(_, e)| e.clone()).collect();
            self.question(what, Ask::Run { edits }, budget_ms, self.options.runs, true)
        };
        let times = self.answered(vec![
            timing("time:before", &[]),
            timing("time:after", &edits),
        ])?;
        let (before, after) = (times[0], times[1]);
        let faster = before.closes()
            && after.closes()
            && after.median_ms() as f64 * self.options.simp_scope_speedup
                <= before.median_ms() as f64;
        Ok(faster.then(|| Narrowed {
            edits,
            before: before.median_ms(),
            after: after.median_ms(),
        }))
    }
}

fn searches<'a>(
    decls: &'a [Decl],
    answers: &'a Answers,
    options: &'a Options,
) -> impl Iterator<Item = Search<'a>> {
    decls.iter().filter(|d| d.ok).map(move |decl| Search {
        decl,
        answers,
        options,
    })
}

impl Lint for SimpScope {
    fn name(&self) -> &'static str {
        "simp_scope"
    }

    fn ask(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Question> {
        searches(decls, answers, options)
            .flat_map(|s| s.check().err().unwrap_or_default())
            .collect()
    }

    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding> {
        searches(decls, answers, options)
            .filter_map(|s| {
                let narrowed = s.check().ok().flatten()?;
                let mut lines = vec![format!(
                    "{} ms instead of {} ms with the simp calls narrowed to the rules they use (medians, alone):",
                    narrowed.after, narrowed.before
                )];
                for (call, edit) in &narrowed.edits {
                    let simp = &s.decl.simps[*call];
                    lines.push(format!("  line {}: `{}` -> `{}`", simp.line, simp.text, edit.text));
                }
                Some(Finding {
                    lint: self.name().to_string(),
                    decl: s.decl.key.clone(),
                    line: s.decl.line,
                    message: lines.join("\n"),
                    edits: narrowed.edits.into_iter().map(|(_, e)| e).collect(),
                })
            })
            .collect()
    }
}
