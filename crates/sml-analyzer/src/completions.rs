use super::*;

fn keyword(s: &str) -> CompletionItem {
    let mut c = CompletionItem::new_simple(s.into(), "SML keyword".into());
    c.kind = Some(CompletionItemKind::Keyword);
    c
}

pub fn keyword_completions() -> Vec<CompletionItem> {
    vec![
        keyword("and"),
        keyword("andalso"),
        keyword("as"),
        keyword("case"),
        keyword("datatype"),
        keyword("do"),
        keyword("else"),
        keyword("end"),
        keyword("exception"),
        keyword("fn"),
        keyword("fun"),
        keyword("functor"),
        keyword("handle"),
        keyword("if"),
        keyword("in"),
        keyword("infix"),
        keyword("infixr"),
        keyword("let"),
        keyword("local"),
        keyword("nonfix"),
        keyword("of"),
        keyword("op"),
        keyword("open"),
        keyword("orelse"),
        keyword("primitive"),
        keyword("raise"),
        keyword("rec"),
        keyword("then"),
        keyword("type"),
        keyword("val"),
        keyword("with"),
        keyword("withtype"),
        keyword("while"),
        keyword("sig"),
        keyword("signature"),
        keyword("struct"),
        keyword("structure"),
    ]
}