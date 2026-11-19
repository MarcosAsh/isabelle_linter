//! A step that another tactic or method closes several times faster.

use crate::lint::{Answers, Finding, Lint, Options};
use crate::protocol::{Answer, Ask, Decl, Edit, Question, Step};

pub struct FasterStep;

/// The replacement, with the median ms of the step as written and of it.
struct Faster {
    text: String,
    before: u64,
    after: u64,
}

struct Search<'a> {
    decl: &'a Decl,
    index: usize,
    step: &'a Step,
    answers: &'a Answers,
    options: &'a Options,
}

impl Search<'_> {
    fn key(&self, what: &str) -> String {
        format!("{}:{}:{what}", self.decl.key, self.step.range.start)
    }

    fn question(&self, what: &str, ask: Ask, timeout_ms: u64, runs: u32, serial: bool) -> Question {
        Question {
            key: self.key(what),
            decl: self.decl.key.clone(),
            ask,
            timeout_ms,
            runs,
            serial,
        }
    }

    fn try_step(
        &self,
        what: &str,
        text: &str,
        timeout_ms: u64,
        runs: u32,
        serial: bool,
    ) -> Question {
        let ask = Ask::Step {
            step: self.index,
            text: text.to_string(),
        };
        self.question(&format!("{what}{text}"), ask, timeout_ms, runs, serial)
    }

    /// Time the step as written, then search if it is slow enough.
    fn check(&self) -> Result<Option<Faster>, Vec<Question>> {
        let original = self.try_step("", &self.step.text, self.options.timeout_ms, 1, false);
        match self.answers.get(&original.key) {
            None => Err(vec![original]),
            Some(answer)
                if !answer.closes() || answer.median_ms() < self.options.faster_step_slow_ms =>
            {
                Ok(None)
            }
            Some(answer) => self.search(answer),
        }
    }

    /// Each candidate gets the original's time over the speed-up. The fastest is timed again,
    /// since the first times are noisy, and its declaration is checked whole with it.
    fn search(&self, original: &Answer) -> Result<Option<Faster>, Vec<Question>> {
        let limit =
            ((original.median_ms() as f64 / self.options.faster_step_speedup) as u64).max(1);
        let suggest = self.question(
            "suggest",
            Ask::Suggest { step: self.index },
            self.options.timeout_ms,
            1,
            false,
        );
        let Some(suggested) = self.answers.get(&suggest.key) else {
            return Err(vec![suggest]);
        };

        let mut texts: Vec<&String> = Vec::new();
        for text in self.step.candidates.iter().chain(&suggested.suggestions) {
            if *text != self.step.text && !texts.contains(&text) {
                texts.push(text);
            }
        }
        let tries: Vec<(&String, Question)> = texts
            .iter()
            .map(|t| (*t, self.try_step("", t, limit, 1, false)))
            .collect();
        let missing: Vec<Question> = tries
            .iter()
            .filter(|(_, q)| !self.answers.contains_key(&q.key))
            .map(|(_, q)| q.clone())
            .collect();
        if !missing.is_empty() {
            return Err(missing);
        }
        let fastest = tries
            .iter()
            .filter(|(_, q)| self.answers[&q.key].closes())
            .min_by_key(|(_, q)| self.answers[&q.key].median_ms());
        match fastest {
            None => Ok(None),
            Some((text, _)) => self.confirm(text, original),
        }
    }

    /// Each run gets twice the original's time.
    fn confirm(&self, text: &str, original: &Answer) -> Result<Option<Faster>, Vec<Question>> {
        let limit = (original.median_ms() * 2).max(1000);
        let before = self.try_step(
            "time:before:",
            &self.step.text,
            limit,
            self.options.runs,
            true,
        );
        let after = self.try_step("time:after:", text, limit, self.options.runs, true);
        let whole = self.question(
            &format!("check:{text}"),
            Ask::Run {
                edits: vec![self.edit(text)],
            },
            self.options.timeout_ms,
            1,
            false,
        );
        let answered = |q: &Question| self.answers.get(&q.key);
        let (Some(b), Some(a), Some(w)) = (answered(&before), answered(&after), answered(&whole))
        else {
            return Err([before, after, whole]
                .into_iter()
                .filter(|q| !self.answers.contains_key(&q.key))
                .collect());
        };
        let faster = b.closes()
            && a.closes()
            && w.closes()
            && (a.median_ms() as f64) * self.options.faster_step_speedup < b.median_ms() as f64;
        Ok(faster.then(|| Faster {
            text: text.to_string(),
            before: b.median_ms(),
            after: a.median_ms(),
        }))
    }

    fn edit(&self, text: &str) -> Edit {
        Edit {
            range: self.step.range,
            text: text.to_string(),
        }
    }
}

fn searches<'a>(
    decls: &'a [Decl],
    answers: &'a Answers,
    options: &'a Options,
) -> impl Iterator<Item = Search<'a>> {
    decls.iter().filter(|d| d.ok).flat_map(move |decl| {
        decl.steps
            .iter()
            .enumerate()
            .map(move |(index, step)| Search {
                decl,
                index,
                step,
                answers,
                options,
            })
    })
}

impl Lint for FasterStep {
    fn name(&self) -> &'static str {
        "faster_step"
    }

    fn ask(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Question> {
        searches(decls, answers, options)
            .flat_map(|s| s.check().err().unwrap_or_default())
            .collect()
    }

    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding> {
        searches(decls, answers, options)
            .filter_map(|s| {
                let faster = s.check().ok().flatten()?;
                let message = format!(
                    "`{}` takes {} ms instead of {} ms for `{}`",
                    faster.text, faster.after, faster.before, s.step.text
                );
                Some(Finding {
                    lint: "faster_step".to_string(),
                    decl: s.decl.key.clone(),
                    line: s.step.line,
                    message,
                    edits: vec![s.edit(&faster.text)],
                })
            })
            .collect()
    }
}
