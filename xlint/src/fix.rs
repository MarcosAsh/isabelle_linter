//! Write fixes into a file. Each fix was checked alone, so the fixes of one declaration go in
//! together only as the lint combined them, and overlapping edits are refused.

use crate::lint::Finding;
use crate::protocol::Edit;

/// The edits of the findings whose fixes touch no earlier finding's, and how many those are.
pub fn disjoint(findings: &[Finding]) -> (Vec<Edit>, usize) {
    let mut edits: Vec<Edit> = Vec::new();
    let mut fixed = 0;
    for finding in findings.iter().filter(|f| !f.edits.is_empty()) {
        let clash = |e: &Edit| {
            edits
                .iter()
                .any(|d| e.range.start < d.range.stop && d.range.start < e.range.stop)
        };
        if !finding.edits.iter().any(clash) {
            edits.extend(finding.edits.iter().cloned());
            fixed += 1;
        }
    }
    (edits, fixed)
}

pub fn apply(text: &str, edits: &[Edit]) -> Result<String, String> {
    let mut edits: Vec<&Edit> = edits.iter().collect();
    edits.sort_by_key(|e| (e.range.start, e.range.stop));
    edits.dedup();
    if edits
        .windows(2)
        .any(|pair| pair[0].range.stop > pair[1].range.start)
    {
        return Err("overlapping edits".to_string());
    }
    let mut fixed = text.to_string();
    for edit in edits.iter().rev() {
        if edit.range.stop > fixed.len()
            || !fixed.is_char_boundary(edit.range.start)
            || !fixed.is_char_boundary(edit.range.stop)
        {
            return Err(format!(
                "edit {}-{} does not fit the file",
                edit.range.start, edit.range.stop
            ));
        }
        fixed.replace_range(edit.range.start..edit.range.stop, &edit.text);
    }
    Ok(fixed)
}
