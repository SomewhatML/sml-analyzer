use super::*;

struct LineIndex<'s> {
    source: &'s str,
    lines: Vec<u64>,
}

impl<'s> LineIndex<'s> {
    fn new(source: &'s str) -> LineIndex {
        let mut lines = vec![0];
        let mut abs = 0;
        for ch in source.chars() {
            if ch == '\n' {
                lines.push(abs);
            }
            abs += 1;
        }
        LineIndex { source, lines }
    }
}

// TODO: Absolutely broken
pub fn apply_changes(prev: &mut String, changes: Vec<TextDocumentContentChangeEvent>) {
    for change in changes {
        let idx = LineIndex::new(prev);

        if let Some(range) = change.range {
            let a = idx.lines[range.start.line as usize] + range.start.character;
            let b = idx.lines[range.end.line as usize] + range.end.character;
            prev.replace_range(a as usize..b as usize, &change.text);
        }
    }
}
