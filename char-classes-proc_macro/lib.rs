use std::{convert::identity, iter::{once, Peekable}};

use litrs::{ByteStringLit, StringLit};
use proc_macro::{Delimiter, Group, Ident, Punct, Spacing::*, Span, TokenStream, TokenTree, Literal};

/// Make `compile_error! {"..."}`
#[must_use]
fn err(msg: &str, span: Span) -> TokenStream {
    let s = |mut tt: TokenTree| {
        tt.set_span(span);
        tt
    };

    <TokenStream as FromIterator<TokenTree>>::from_iter([
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("core", span).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("compile_error", span).into(),
        Punct::new('!', Joint).into(),
        Group::new(Delimiter::Brace, s(
            Literal::string(msg).into(),
        ).into()).into(),
    ].map(s))
}

fn matches(stream: TokenStream) -> TokenStream {
    <TokenStream as FromIterator<TokenTree>>::from_iter([
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("core", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("matches", Span::call_site()).into(),
        Punct::new('!', Joint).into(),
        Group::new(Delimiter::Parenthesis, stream).into()
    ])
}

fn tts(tt: impl Into<TokenTree>) -> TokenStream {
    let tt: TokenTree = tt.into();
    TokenStream::from(tt)
}

fn stream(i: impl IntoIterator<Item = TokenTree>) -> TokenStream {
    i.into_iter().collect()
}
fn streams(i: impl IntoIterator<Item = TokenStream>) -> TokenStream {
    i.into_iter().collect()
}

enum Mode {
    Normal,
    Exclude,
    Not(TokenTree),
}

use Mode::*;

impl Mode {
    fn resolve(iter: &mut Peekable<impl Iterator<Item = TokenTree>>) -> Self {
        match iter.peek() {
            Some(TokenTree::Punct(p)) if p.as_char() == '!' => {
                Not(iter.next().unwrap())
            },
            Some(TokenTree::Punct(p)) if p.as_char() == '^' => {
                iter.next().unwrap();
                Exclude
            },
            _ => Normal,
        }
    }

    fn run(
        self,
        expr: TokenStream,
        pat: TokenStream,
        com: TokenTree,
    ) -> TokenStream {
        match self {
            Normal => matches(streams([expr, tts(com), pat])),
            Not(not) => once(not)
                .chain(Normal.run(expr, pat, com))
                .collect(),
            Exclude => stream([
                Ident::new("match", com.span()).into(),
                Group::new(Delimiter::None, expr).into(),
                Group::new(
                    Delimiter::Brace,
                    streams([
                        none(),
                        tts(Punct::new('|', Alone)),
                        pat,
                        stream([
                            Punct::new('=', Joint).into(),
                            Punct::new('>', Alone).into(),
                            Ident::new("false", Span::call_site()).into(),
                            Punct::new(',', Alone).into(),
                        ]),
                        some(tts(Ident::new("_", Span::call_site()))),
                        stream([
                            Punct::new('=', Joint).into(),
                            Punct::new('>', Alone).into(),
                            Ident::new("true", Span::call_site()).into(),
                            Punct::new(',', Alone).into(),
                        ]),
                    ]),
                ).into(),
            ]),
        }
    }
}

fn first_elem(stream: TokenStream) -> TokenStream {
    let stream = [
        TokenStream::from(TokenTree::Punct(Punct::new('&', Joint))),
        stream,
    ].into_iter().collect();
    <TokenStream as FromIterator<TokenTree>>::from_iter([
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("char_classes", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("FirstElem", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("first_elem", Span::call_site()).into(),
        Group::new(Delimiter::Parenthesis, stream).into()
    ])
}

enum Str {
    Norm(String),
    Byte(Vec<u8>),
}

fn lit_str(tt: &TokenTree) -> Result<Str, TokenStream> {
    StringLit::try_from(tt)
        .map(|s| Str::Norm(s.into_value()))
        .map_err(|e| e.to_string())
        .or_else(|e| ByteStringLit::try_from(tt)
            .map(|b| Str::Byte(b.into_value()))
            .map_err(|e2| format!("{e}\n{e2}")))
        .map_err(|e| err(&e, tt.span()))
}

trait Spaned {
    fn spaned(self, span: Span) -> Self;
}
impl Spaned for TokenTree {
    fn spaned(mut self, span: Span) -> Self {
        self.set_span(span);
        self
    }
}
impl Spaned for Literal {
    fn spaned(mut self, span: Span) -> Self {
        self.set_span(span);
        self
    }
}
impl Spaned for Punct {
    fn spaned(mut self, span: Span) -> Self {
        self.set_span(span);
        self
    }
}

trait ToPat: Sized {
    fn to_pat(self, span: Span) -> TokenStream;
}
impl ToPat for u8 {
    fn to_pat(self, span: Span) -> TokenStream {
        TokenTree::from(Literal::byte_character(self).spaned(span)).into()
    }
}
impl ToPat for char {
    fn to_pat(self, span: Span) -> TokenStream {
        TokenTree::from(Literal::character(self).spaned(span)).into()
    }
}
impl<T: ToPat> ToPat for (T, T) {
    fn to_pat(self, span: Span) -> TokenStream {
        let (from, to) = self;
        TokenStream::from_iter([
            from.to_pat(span),
            <TokenStream as FromIterator<TokenTree>>::from_iter([
                Punct::new('.', Joint).into(),
                Punct::new('.', Joint).into(),
                Punct::new('=', Joint).into(),
            ]),
            to.to_pat(span),
        ])
    }
}

trait IsDash {
    fn is_dash(&self) -> bool;
}
impl IsDash for u8 {
    fn is_dash(&self) -> bool {
        *self == b'-'
    }
}
impl IsDash for char {
    fn is_dash(&self) -> bool {
        *self == '-'
    }
}

trait Expected: Iterator<Item = TokenTree> + Sized {
    fn expected(&mut self, ty: &str) -> Result<TokenTree, TokenStream> {
        self.next()
            .ok_or_else(||
        {
            let msg = format!("unexpected end of input, expected a {ty}");
            err(&msg, Span::call_site())
        })
    }
}
impl<T: Iterator<Item = TokenTree>> Expected for T { }

fn none() -> TokenStream {
    stream([
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("core", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("option", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("Option", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("None", Span::call_site()).into(),
    ])
}

fn some(input: TokenStream) -> TokenStream {
    stream([
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("core", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("option", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("Option", Span::call_site()).into(),
        Punct::new(':', Joint).into(),
        Punct::new(':', Joint).into(),
        Ident::new("Some", Span::call_site()).into(),
        Group::new(Delimiter::Parenthesis, input).into(),
    ])
}

fn to_pats<T, I>(iter: I, span: Span) -> Result<TokenStream, TokenStream>
where T: ToPat + IsDash,
      I: IntoIterator<Item = T>,
{
    let mut iter = iter.into_iter().peekable();
    let Some(mut first) = iter.next() else {
        return Err(err("not support empty pattern", span));
    };
    let mut result = TokenStream::new();
    let mut sep: fn(&mut TokenStream) = |_| ();

    while let Some(cur) = iter.next() {
        sep(&mut result);

        if let Some(to) = iter.next_if(|_| cur.is_dash()) {
            result.extend([(first, to).to_pat(span)]);

            if let Some(next) = iter.next() {
                first = next;
            } else {
                return Ok(some(result));
            }
        } else {
            result.extend([first.to_pat(span)]);
            first = cur;
        }

        sep = |result| {
            result.extend([TokenTree::from(Punct::new('|', Alone))]);
        };
    }

    sep(&mut result);
    result.extend([first.to_pat(span)]);
    Ok(some(result))
}

/// Like `char_classes::any()`, expand into `match` for better performance (about 5x)
///
/// - `^"..."` is exclude pattern
/// - `!"..."` like `!any!(...)`
///
/// # Examples
///
/// ```ignore
/// use char_classes::any;
///
/// assert!(any!("ab",      'a'));
/// assert!(any!("ab",      'b'));
/// assert!(any!("ab",      'b'));
/// assert!(any!("a-c",     'a'));
/// assert!(any!("a-c",     'b'));
/// assert!(any!("a-c",     'c'));
/// assert!(any!(b"ab",    b'a'));
/// assert!(any!(b"ab",    b'b'));
///
/// assert!(! any!(^b"ab",   b'b'));
/// assert!(! any!(^"ab",   ""));
/// assert!(any!(!"ab",   ""));
///
/// assert!(any!(b"ab")(b'b'));
/// ```
///
/// **predicate mode**:
///
/// ```ignore
/// use char_classes::any;
///
/// assert!(any!(b"ab")(b"b"));
/// assert!(any!(!b"ab")(b"c"));
/// assert!(any!(^b"ab")(b"c"));
///
/// assert!(any!(!b"ab")(b""));
/// assert!(! any!(^b"ab")(b""));
/// ```
#[proc_macro]
pub fn any(input: TokenStream) -> TokenStream {
    any_impl(input).unwrap_or_else(identity)
}

fn any_impl(input: TokenStream) -> Result<TokenStream, TokenStream> {
    let mut iter = input.into_iter().peekable();
    let mode = Mode::resolve(&mut iter);
    let first = iter.expected("literal")?;
    let lit_str = lit_str(&first)?;

    let pat = match lit_str {
        Str::Norm(s) => to_pats(s.chars(), first.span()),
        Str::Byte(bytes) => to_pats(bytes, first.span()),
    }?;
    let predicate_mode = iter.peek().is_none();
    let com = iter.next()
        .unwrap_or_else(|| Punct::new(',', Alone).into());

    let output = if predicate_mode {
        let name = TokenTree::from(Ident::new("input", first.span()));
        let expr = first_elem(name.clone().into());

        once(Punct::new('|', Joint).into())
            .chain([name, Punct::new('|', Alone).into()])
            .chain(mode.run(expr, pat, com))
            .collect()
    } else {
        mode.run(first_elem(iter.collect()), pat, com)
    };

    Ok(tts(Group::new(Delimiter::None, output)))
}
