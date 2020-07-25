use super::*;

pub struct GlobalState<'arena> {
    text_cache: HashMap<lsp_types::Url, String>,
    kw_completions: Vec<CompletionItem>,
    interner: Interner,
    sender: crossbeam_channel::Sender<lsp_server::Message>,
    arena: &'arena database::arena::Arena<'arena>,
    db: Database<'arena>,
}

pub fn diag_convert(diag: sml_util::diagnostics::Diagnostic) -> Diagnostic {
    let sp = diag.primary.span;
    let message = diag.primary.info;
    let range = Range::new(
        Position::new(sp.start.line as u64, sp.start.col as u64),
        Position::new(sp.end.line as u64, sp.end.col as u64),
    );
    Diagnostic::new_simple(range, message)
}

fn measure<T, F: FnOnce() -> T>(f: F) -> (T, u128) {
    let start = Instant::now();
    let r = f();
    let stop = Instant::now().duration_since(start).as_micros();
    (r, stop)
}

#[inline]
fn in_span(pos: &Position, span: &Span) -> bool {
    if pos.line >= span.start.line as u64 && pos.line <= span.end.line as u64 {
        pos.character >= span.start.col as u64 && pos.character <= span.end.col as u64
    } else {
        false
    }
}

impl<'a> GlobalState<'a> {
    pub fn new(
        arena: &'a database::arena::Arena<'a>,
        sender: crossbeam_channel::Sender<Message>,
    ) -> GlobalState<'a> {
        GlobalState {
            text_cache: HashMap::default(),
            kw_completions: completions::keyword_completions(),
            interner: Interner::with_capacity(4096),
            sender,
            arena,
            db: Database::new(arena),
        }
    }

    pub fn parse(&mut self, url: &Url) {
        let data = match self.text_cache.get(url) {
            Some(data) => data,
            None => return,
        };

        let mut parser = sml_frontend::parser::Parser::new(data, &mut self.interner);
        let ((res, diags), dur) = measure(|| (parser.parse_decl(), parser.diags));
        // info!("parsing took {} us", dur);

        let mut st_diag = Vec::new();
        match res {
            Ok(d) => {
                if !diags.is_empty() {
                    for diag in diags {
                        st_diag.push(diag_convert(diag));
                    }
                }
                self.db = Database::new(self.arena);
                let (_, dur) = measure(|| self.db.walk_decl(&d));
                // info!("new elab took {} us", dur);

                let diags = std::mem::replace(&mut self.db.diags, Vec::new());
                if !diags.is_empty() {
                    for diag in diags {
                        st_diag.push(diag_convert(diag));
                    }
                }
            }
            Err(e) => {
                st_diag.push(diag_convert(e.to_diagnostic()));
                if !diags.is_empty() {
                    for diag in diags {
                        st_diag.push(diag_convert(diag));
                    }
                }
            }
        };

        // info!("reporting {} errors for {:?}", st_diag.len(), url);

        self.send_notification::<lsp_types::notification::PublishDiagnostics>(
            lsp_types::PublishDiagnosticsParams {
                uri: url.clone(),
                diagnostics: st_diag,
                version: None,
            },
        );
    }

    pub(crate) fn send_notification<N: lsp_types::notification::Notification>(
        &mut self,
        params: N::Params,
    ) where
        N::Params: Serialize,
    {
        let not = lsp_server::Notification::new(N::METHOD.to_string(), params);
        self.send(not.into());
    }

    fn send(&self, message: lsp_server::Message) {
        self.sender.send(message).unwrap()
    }
}

impl<'a> GlobalState<'a> {
    fn map_values(&self, sym: Symbol, ty: &database::Type<'_>) -> Option<CompletionItem> {
        let name = self.interner.get(sym)?;
        let mut alpha = types::Alpha::default();
        let mut out = String::new();
        alpha.write_type2(ty, &self.interner, &mut out).ok()?;

        let mut c = CompletionItem::new_simple(name.into(), format!("{}: {}", name, out));
        c.kind = Some(CompletionItemKind::Value);
        Some(c)
    }

    fn map_types(&self, sym: Symbol, ty: Option<&database::Type<'_>>) -> Option<CompletionItem> {
        let name = self.interner.get(sym)?;
        let mut c = if let Some(ty) = ty {
            let mut alpha = types::Alpha::default();
            let mut out = String::new();
            alpha.write_type2(ty, &self.interner, &mut out).ok()?;
            CompletionItem::new_simple(name.into(), format!("{}: {}", name, out))
        } else {
            CompletionItem::new_simple(name.into(), format!("{}", name))
        };
        c.kind = Some(CompletionItemKind::TypeParameter);
        c.insert_text = Some(format!(" {}", &c.label));
        Some(c)
    }

    pub fn open(&mut self, params: DidOpenTextDocumentParams) {
        self.text_cache
            .insert(params.text_document.uri.clone(), params.text_document.text);
        self.parse(&params.text_document.uri);
    }

    pub fn update(&mut self, params: DidChangeTextDocumentParams) {
        match self.text_cache.get_mut(&params.text_document.uri) {
            Some(data) => util::apply_changes(data, params.content_changes),
            None => {}
        }
    }

    fn position_to_type(&self, pos: Position) -> Option<&'a database::Type<'a>> {
        self.db
            .bindings
            .iter()
            .filter(|(sp, _)| in_span(&pos, sp))
            .last()
            .map(|(_, ty)| *ty)
    }

    pub fn hover_request(&mut self, params: TextDocumentPositionParams) -> Option<Hover> {
        self.position_to_type(params.position).map(|ty| {
            let mut alpha = types::Alpha::default();
            let mut out = String::with_capacity(64);

            alpha.write_type2(ty, &self.interner, &mut out).unwrap();

            Hover {
                contents: HoverContents::Scalar(MarkedString::from_markdown(format!(
                    "type: {}",
                    out
                ))),
                range: None,
            }
        })
    }

    pub fn completion_req(&mut self, params: CompletionParams) -> Option<CompletionResponse> {
        let pos = params.text_document_position.position;
        let loc = sml_util::span::Location::new(pos.line as u16, pos.character as u16, 0);
        params.context.map(
            |ctx| match ctx.trigger_character.map(|s| s.chars().next()).flatten() {
                Some(':') => {
                    let tycons = self
                        .db
                        .in_scope_types(loc)
                        .into_iter()
                        .filter_map(|(sym, ty)| self.map_types(sym, ty))
                        .collect::<Vec<CompletionItem>>();
                    CompletionResponse::Array(tycons)
                }
                _ => {
                    let tycons = self
                        .db
                        .in_scope_values(loc)
                        .into_iter()
                        .filter_map(|(sym, ty)| self.map_values(sym, ty))
                        .chain(self.kw_completions.clone())
                        .collect::<Vec<CompletionItem>>();

                    CompletionResponse::Array(tycons)
                }
            },
        )
    }
}
