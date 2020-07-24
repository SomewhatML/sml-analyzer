use super::*;

pub fn request<'a>(r: Request, conn: &'a Connection) -> RequestDispatch {
    RequestDispatch {
        data: Some(r),
        conn,
    }
}

pub fn notification(n: Notification) -> NotificationDispatch {
    NotificationDispatch { data: Some(n) }
}

pub struct NotificationDispatch {
    data: Option<Notification>,
}

impl NotificationDispatch {
    pub fn handle<R, F>(&mut self, f: F) -> &mut Self
    where
        R: lsp_types::notification::Notification,
        R::Params: serde::de::DeserializeOwned,
        F: FnOnce(R::Params),
    {
        let n = match self.data.take() {
            Some(n) => n,
            None => return self,
        };

        let n = match cast_not::<R>(n) {
            Ok(params) => {
                f(params);
                return self;
            }
            Err(not) => not,
        };
        self.data = Some(n);
        self
    }
}

pub struct RequestDispatch<'a> {
    data: Option<Request>,
    conn: &'a Connection,
}

impl<'a> RequestDispatch<'a> {
    pub fn handle<R, F, T>(
        &mut self,
        f: F,
    ) -> Result<&mut Self, crossbeam_channel::SendError<Message>>
    where
        R: lsp_types::request::Request,
        R::Params: serde::de::DeserializeOwned,
        T: serde::ser::Serialize,
        F: FnOnce(R::Params) -> T,
    {
        let n = match self.data.take() {
            Some(n) => n,
            None => return Ok(self),
        };

        let n = match cast::<R>(n) {
            Ok((id, params)) => {
                let result = f(params);
                let result = serde_json::to_value(&result).unwrap();
                let resp = Response {
                    id,
                    result: Some(result),
                    error: None,
                };
                self.conn.sender.send(Message::Response(resp))?;
                return Ok(self);
            }
            Err(not) => not,
        };
        self.data = Some(n);
        Ok(self)
    }
}

fn cast<R>(req: Request) -> Result<(RequestId, R::Params), Request>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}

fn cast_not<R>(req: Notification) -> Result<R::Params, Notification>
where
    R: lsp_types::notification::Notification,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}
