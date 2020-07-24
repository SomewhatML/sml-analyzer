use super::*;

fn ty(s: &str) -> CompletionItem {
    let mut c = CompletionItem::new_simple(s.into(), "SML type".into());
    c.kind = Some(CompletionItemKind::TypeParameter);
    c
}

fn keyword(s: &str) -> CompletionItem {
    let mut c = CompletionItem::new_simple(s.into(), "SML keyword".into());
    c.kind = Some(CompletionItemKind::Keyword);
    c
}

pub fn fun(s: &str, ty_str: &str) -> CompletionItem {
    let mut c = CompletionItem::new_simple(s.into(), ty_str.into());
    c.kind = Some(CompletionItemKind::Function);
    // c.documentation = Some(Documentation::MarkupContent(MarkupContent ))
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

pub fn builtin_ty_completions() -> Vec<CompletionItem> {
    vec![
        ty("unit"),
        ty("int"),
        ty("bool"),
        ty("char"),
        ty("string"),
        ty("list"),
        ty("ref"),
    ]
}
