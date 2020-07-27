use super::*;

pub fn loc_to_position(loc: sml_util::span::Location) -> lsp_types::Position {
    Position::new(loc.line as u64, loc.col as u64)
}

pub fn position_to_loc(pos: lsp_types::Position) -> sml_util::span::Location {
    sml_util::span::Location::new(pos.line as u16, pos.character as u16, 0)
}

pub fn span_to_range(span: Span) -> Range {
    let start = loc_to_position(span.start);
    let end = loc_to_position(span.end);
    Range::new(start, end)
}

struct LineIndex<'s> {
    source: &'s str,
    lines: Vec<u64>,
}

impl<'s> LineIndex<'s> {
    fn new(source: &'s str) -> LineIndex {
        let mut lines = vec![0];
        let mut abs = 0;
        for ch in source.chars() {
            abs += 1;
            if ch == '\n' {
                lines.push(abs);
            }
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
