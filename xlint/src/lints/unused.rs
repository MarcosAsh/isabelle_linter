//! Pieces a proof does not need, found by checking the declaration again without them.

use crate::lint::{Answers, Finding, Lint, Options};
use crate::protocol::{Ask, Decl, Edit, Piece, Question};

pub struct Unused;

/// A piece that changes the statement is reported, but never part of the fix.
const STATEMENT: &str = "assumption";
/// A piece other deletions can free, like a `have` nothing uses any more.
const FREED: &str = "have";

/// Questions still to ask, or the indexes of the unneeded pieces.
type Search = Result<Vec<usize>, Vec<Question>>;

struct Unneeded {
    pieces: Vec<usize>,
    /// Median ms as written and with the fix, if they were timed.
    medians: Option<(u64, u64)>,
}

/// One deletion per piece, without the pieces that lie inside another one.
fn deletions(decl: &Decl, pieces: &[usize]) -> Vec<Edit> {
    let range = |i: usize| decl.pieces[i].range;
    let mut outer: Vec<usize> = pieces
        .iter()
        .copied()
        .filter(|&i| {
            !pieces
                .iter()
                .any(|&j| j != i && range(j) != range(i) && range(j).contains(&range(i)))
        })
        .collect();
    outer.sort();
    outer.dedup_by_key(|i| range(*i));
    outer
        .into_iter()
        .map(|i| Edit {
            range: range(i),
            text: String::new(),
        })
        .collect()
}

fn run(
    decl: &Decl,
    what: &str,
    dropped: &[usize],
    timeout_ms: u64,
    runs: u32,
    serial: bool,
) -> Question {
    let edits = deletions(decl, dropped);
    Question {
        key: format!("{}:{what}", decl.key),
        decl: decl.key.clone(),
        ask: Ask::Run { edits },
        timeout_ms,
        runs,
        serial,
    }
}

struct Pieces<'a> {
    decl: &'a Decl,
    answers: &'a Answers,
    budget_ms: u64,
    ahead: usize,
}

impl Pieces<'_> {
    fn drop(&self, pieces: &[usize]) -> Question {
        let mut sorted = pieces.to_vec();
        sorted.sort();
        let names: Vec<String> = sorted.iter().map(usize::to_string).collect();
        run(
            self.decl,
            &format!("drop:{}", names.join(",")),
            pieces,
            self.budget_ms,
            1,
            false,
        )
    }

    fn inside(&self, pieces: &[usize], piece: usize) -> bool {
        pieces.iter().any(|&p| {
            self.decl.pieces[p]
                .range
                .contains(&self.decl.pieces[piece].range)
        })
    }

    /// Each piece alone, then all the unneeded ones at once, else one at a time. The deletions
    /// may free pieces that were needed before.
    fn search(&self) -> Search {
        let all: Vec<usize> = (0..self.decl.pieces.len()).collect();
        let alone: Vec<Question> = all.iter().map(|&i| self.drop(&[i])).collect();
        let missing: Vec<Question> = alone
            .iter()
            .filter(|q| !self.answers.contains_key(&q.key))
            .cloned()
            .collect();
        if !missing.is_empty() {
            return Err(missing);
        }
        let closes = |i: &usize| self.answers[&alone[*i].key].closes();
        let kind = |i: &usize| self.decl.pieces[*i].kind.as_str();
        let (unneeded, needed): (Vec<usize>, Vec<usize>) = all.iter().partition(|i| closes(i));
        let (statement, others): (Vec<usize>, Vec<usize>) =
            unneeded.iter().partition(|i| kind(i) == STATEMENT);
        let freeable: Vec<usize> = needed.into_iter().filter(|i| kind(i) == FREED).collect();

        let kept = self.combine(&[], &others)?;
        let freed = self.one_by_one(&kept, &freeable)?;
        let base = [kept, freed].concat();
        let more = self.combine(&base, &statement)?;
        Ok([base, more].concat())
    }

    /// On top of base: all pieces at once, else one at a time.
    fn combine(&self, base: &[usize], pieces: &[usize]) -> Search {
        if pieces.is_empty() {
            return Ok(Vec::new());
        }
        let all = self.drop(&[base, pieces].concat());
        match self.answers.get(&all.key) {
            None => Err(vec![all]),
            Some(answer) if answer.closes() => Ok(pieces.to_vec()),
            Some(_) => self.one_by_one(base, pieces),
        }
    }

    fn one_by_one(&self, base: &[usize], pieces: &[usize]) -> Search {
        let mut kept: Vec<usize> = Vec::new();
        for (n, &piece) in pieces.iter().enumerate() {
            let so_far = [base, &kept[..]].concat();
            if self.inside(&so_far, piece) {
                continue;
            }
            match self
                .answers
                .get(&self.drop(&[&so_far[..], &[piece]].concat()).key)
            {
                None => return Err(self.guesses(base, &kept, &pieces[n..])),
                Some(answer) if answer.closes() => kept.push(piece),
                Some(_) => {}
            }
        }
        Ok(kept)
    }

    /// The next questions of one_by_one, each as if the ones before it can go. While pieces can
    /// go they are asked anyway, so a declaration takes a round per needed piece, not per piece.
    fn guesses(&self, base: &[usize], kept: &[usize], rest: &[usize]) -> Vec<Question> {
        let mut guessed = kept.to_vec();
        let mut questions = Vec::new();
        for &piece in rest {
            let so_far = [base, &guessed[..]].concat();
            if questions.len() >= self.ahead.max(1) || self.inside(&so_far, piece) {
                continue;
            }
            guessed.push(piece);
            questions.push(self.drop(&[&so_far[..], &[piece]].concat()));
        }
        questions
    }
}

/// Run the declaration as written, which sets the budget; search; then time the fix, since a
/// deletion can make a proof slower.
fn check(decl: &Decl, answers: &Answers, options: &Options) -> Result<Unneeded, Vec<Question>> {
    let original = run(decl, "original", &[], options.timeout_ms, 1, false);
    let Some(answer) = answers.get(&original.key) else {
        return Err(vec![original]);
    };
    if !answer.closes() {
        return Ok(Unneeded {
            pieces: Vec::new(),
            medians: None,
        });
    }
    let budget_ms = options.budget_ms(answer);
    let pieces = Pieces {
        decl,
        answers,
        budget_ms,
        ahead: options.unused_ahead,
    }
    .search()?;
    let fixed = fix(decl, &pieces);
    if fixed.is_empty() {
        return Ok(Unneeded {
            pieces,
            medians: None,
        });
    }
    let before = run(decl, "time:before", &[], budget_ms, options.runs, true);
    let after = run(decl, "time:after", &fixed, budget_ms, options.runs, true);
    match (answers.get(&before.key), answers.get(&after.key)) {
        (Some(b), Some(a)) => {
            let medians = (b.closes() && a.closes()).then(|| (b.median_ms(), a.median_ms()));
            Ok(Unneeded { pieces, medians })
        }
        _ => Err(vec![before, after]),
    }
}

fn fix(decl: &Decl, pieces: &[usize]) -> Vec<usize> {
    pieces
        .iter()
        .copied()
        .filter(|&i| decl.pieces[i].kind != STATEMENT)
        .collect()
}

fn describe(piece: &Piece) -> String {
    format!("  {} `{}` (line {})", piece.kind, piece.text, piece.line)
}

fn finding(decl: &Decl, unneeded: &Unneeded) -> Finding {
    let mut pieces = unneeded.pieces.clone();
    pieces.sort();
    let (statement, others): (Vec<usize>, Vec<usize>) = pieces
        .iter()
        .partition(|&&i| decl.pieces[i].kind == STATEMENT);
    let mut lines = Vec::new();
    if !others.is_empty() {
        lines.push("not needed:".to_string());
        lines.extend(others.iter().map(|&i| describe(&decl.pieces[i])));
    }
    if let Some((before, after)) = unneeded.medians {
        lines.push(format!(
            "time: {before} ms as written, {after} ms with the fix (medians, alone)"
        ));
    }
    if !statement.is_empty() {
        lines.push("not needed, but removing them changes the statement:".to_string());
        lines.extend(statement.iter().map(|&i| describe(&decl.pieces[i])));
    }
    let edits = deletions(decl, &others);
    Finding {
        lint: "unused".to_string(),
        decl: decl.key.clone(),
        line: decl.line,
        message: lines.join("\n"),
        edits,
    }
}

impl Lint for Unused {
    fn name(&self) -> &'static str {
        "unused"
    }

    fn ask(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Question> {
        decls
            .iter()
            .filter(|d| d.ok)
            .flat_map(|d| check(d, answers, options).err().unwrap_or_default())
            .collect()
    }

    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding> {
        decls
            .iter()
            .filter(|d| d.ok)
            .filter_map(|d| {
                check(d, answers, options)
                    .ok()
                    .filter(|u| !u.pieces.is_empty())
                    .map(|u| finding(d, &u))
            })
            .collect()
    }
}
