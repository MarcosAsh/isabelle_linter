//! Write fixes into a file. Each fix was checked alone, so the fixes of one declaration go in
//! together only as the lint combined them, and overlapping edits are refused.

use crate::protocol::Edit;

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
