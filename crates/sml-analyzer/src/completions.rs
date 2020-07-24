use super::*;

fn ty(s: &str) -> CompletionItem {
    let mut c = CompletionItem::new_simple(s.into(), "primitive type".into());
    c.kind = Some(CompletionItemKind::TypeParameter);
    c
}

fn keyword(s: &str) -> CompletionItem {
    let mut c = CompletionItem::new_simple(s.into(), "keyword".into());
    c.kind = Some(CompletionItemKind::Keyword);
    c
}

mod snippets {
    use super::*;

    #[inline]
    fn template(kw: &str, snippet: &str) -> CompletionItem {
        CompletionItem {
            label: kw.into(),
            detail: Some(kw.into()),
            kind: Some(CompletionItemKind::Keyword),
            insert_text_format: Some(InsertTextFormat::Snippet),
            insert_text: Some(format!("{} {}", kw, snippet)),
            ..CompletionItem::default()
        }
    }

    pub fn decl_let() -> CompletionItem {
        template("let", "${1:declaration} in ${2:expr} end$0")
    }

    pub fn decl_local() -> CompletionItem {
        template("local", "${1:declaration} in ${2:expr} end$0")
    }

    pub fn expr_case() -> CompletionItem {
        template("case", "${1:expr} of\n| ${2:pat} => ${3:expr}\nend$0")
    }

    pub fn expr_fn() -> CompletionItem {
        template("fn", "${1:arg} => ${0:body}")
    }

    pub fn expr_if() -> CompletionItem {
        template(
            "if",
            "${1:condition} then ${2:consquence} else ${0:alternate}",
        )
    }
}

pub fn keyword_completions() -> Vec<CompletionItem> {
    vec![
        keyword("and"),
        keyword("andalso"),
        keyword("as"),
        snippets::expr_case(),
        keyword("datatype"),
        keyword("do"),
        keyword("else"),
        keyword("end"),
        keyword("exception"),
        snippets::expr_fn(),
        keyword("fun"),
        keyword("functor"),
        keyword("handle"),
        snippets::expr_if(),
        keyword("in"),
        keyword("infix"),
        keyword("infixr"),
        snippets::decl_let(),
        snippets::decl_local(),
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
