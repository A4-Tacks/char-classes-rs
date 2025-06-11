use std::{convert::identity, iter::once};

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
        .map(|s| Str::Norm(s.into_value().into_owned()))
        .map_err(|e| e.to_string())
        .or_else(|e| ByteStringLit::try_from(tt)
            .map(|b| Str::Byte(b.into_value().into_owned()))
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

fn some(stream: TokenStream, span: Span) -> TokenStream {
    TokenStream::from_iter([
        TokenTree::from(Ident::new("Some", span)),
        TokenTree::from(Group::new(Delimiter::Parenthesis, stream)),
    ])
}

fn to_pats<T, I>(iter: I, span: Span) -> Result<TokenStream, TokenStream>
where T: ToPat + IsDash,
      I: IntoIterator<Item = T>,
{
    let mut iter = iter.into_iter().peekable();
    let Some(mut first) = iter.next() else {
        return Err(err("cannot support empty pattern", span));
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
                return Ok(some(result, span));
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
    Ok(some(result, span))
}

/// Like `char_classes::any()`, expand into [`matches`] for better performance
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
///
/// assert!(any!(b"ab")(b'b'));
/// ```
#[proc_macro]
pub fn any(input: TokenStream) -> TokenStream {
    let mut iter = input.into_iter().peekable();
    let not = iter.next_if(|tt| {
        matches!(tt, TokenTree::Punct(p) if p.as_char() == '^')
    }).map(|tt| Punct::new('!', Joint).spaned(tt.span()).into());
    let Some(first) = iter.next() else {
        return err("unexpected end of input, expected a literal", Span::call_site());
    };
    let comma = iter.next();
    if comma.as_ref().is_some_and(|comma| {
        !matches!(&comma, TokenTree::Punct(p) if p.as_char() == ',')
    }) {
        return err("unexpected token, expected a comma", comma.unwrap().span());
    }
    let lit_str = match lit_str(&first) {
        Ok(s) => s,
        Err(e) => return e,
    };
    match lit_str {
        Str::Norm(s) => to_pats(s.chars(), first.span()),
        Str::Byte(bytes) => to_pats(bytes, first.span()),
    }.map_or_else(identity, |pat| {
        if let Some(comma) = comma {
            let expr = not.into_iter().chain(matches(
                first_elem(iter.collect())
                    .into_iter()
                    .chain([comma])
                    .chain(pat)
                    .collect(),
            )).collect();

            TokenTree::from(Group::new(Delimiter::None, expr)).into()
        } else {
            let name = TokenTree::from(Ident::new("input", first.span()));
            let mut comma = Punct::new(',', Alone);
            comma.set_span(first.span());

            let expr = once(Punct::new('|', Joint).into())
                .chain([name.clone(), Punct::new('|', Alone).into()])
                .chain(not)
                .chain(matches(first_elem(name.into())
                        .into_iter()
                        .chain([comma.into()])
                        .chain(pat)
                        .collect()))
                .collect();
            TokenTree::from(Group::new(Delimiter::None, expr)).into()
        }
    })
}
