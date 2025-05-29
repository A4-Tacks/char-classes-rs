#![no_std]
#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]

/// Like [`any()`], expand into [`matches`] for better performance
///
/// # Examples
///
/// ```
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
/// ```
///
#[cfg(feature = "macros")]
#[cfg_attr(docsrs, doc(cfg(feature = "macros")))]
pub use char_classes_proc_macro::any;

#[doc = include_str!("../README.md")]
pub trait MatchOne: FirstElem {
    type Pattern: ?Sized;

    /// Match one element or first element
    ///
    /// Match `'-'` Please write at the beginning or end, e.g `"a-z-"`
    ///
    /// # Examples
    ///
    /// ```
    /// # use char_classes::MatchOne;
    /// assert_eq!(Some('a'), 'a'.match_one("a-c"));
    /// assert_eq!(Some('b'), 'b'.match_one("a-c"));
    /// assert_eq!(None,      '-'.match_one("a-c"));
    /// assert_eq!(Some('-'), '-'.match_one("a-"));
    ///
    /// assert_eq!(Some('a'), "ab".match_one("a"));
    /// assert_eq!(None,      "ab".match_one("b"));
    /// ```
    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out>;

    /// Call [`.match_one(pattern).is_some()`](#tymethod.match_one)
    fn is_match_one(&self, pattern: &Self::Pattern) -> bool {
        self.match_one(pattern).is_some()
    }
}

impl<T: MatchOne> MatchOne for Option<T> {
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.as_ref().and_then(|val| val.match_one(pattern))
    }
}

impl<T: MatchOne + ?Sized> MatchOne for &T {
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        (**self).match_one(pattern)
    }
}

impl<T: MatchOne + ?Sized> MatchOne for &mut T {
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        (**self).match_one(pattern)
    }
}

impl MatchOne for char {
    type Pattern = str;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        match_impl(pattern.chars(), self).then_some(*self)
    }
}

impl MatchOne for u8 {
    type Pattern = [u8];

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        match_impl(pattern.iter().copied(), self).then_some(*self)
    }
}

impl MatchOne for str {
    type Pattern = str;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.chars().next().match_one(pattern)
    }
}

impl MatchOne for () {
    type Pattern = ();

    fn match_one(&self, _pattern: &Self::Pattern) -> Option<Self::Out> {
        None
    }
}

impl<T: MatchOne> MatchOne for [T] {
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.first().match_one(pattern)
    }
}

impl<T: MatchOne, const N: usize> MatchOne for [T; N] {
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.first().match_one(pattern)
    }
}

macro_rules! impl_first_elem_trivial {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl FirstElem for $ty {
                type Out = $ty;

                fn first_elem(&self) -> Option<Self::Out> {
                    Some(*self)
                }
            }
        )+
    };
}

/// Get the first element
pub trait FirstElem {
    type Out;

    fn first_elem(&self) -> Option<Self::Out>;
}

impl_first_elem_trivial! {
    u8,
    u16,
    u32,
    u64,
    u128,
    i8,
    i16,
    i32,
    i64,
    i128,
    char,
    f32,
    f64,
}

impl FirstElem for () {
    type Out = core::convert::Infallible;

    fn first_elem(&self) -> Option<Self::Out> {
        None
    }
}

impl<T: FirstElem + ?Sized> FirstElem for &T {
    type Out = T::Out;

    fn first_elem(&self) -> Option<Self::Out> {
        (**self).first_elem()
    }
}

impl<T: FirstElem + ?Sized> FirstElem for &mut T {
    type Out = T::Out;

    fn first_elem(&self) -> Option<Self::Out> {
        (**self).first_elem()
    }
}

impl<T: FirstElem> FirstElem for Option<T> {
    type Out = T::Out;

    fn first_elem(&self) -> Option<Self::Out> {
        self.as_ref().and_then(T::first_elem)
    }
}

impl FirstElem for str {
    type Out = char;

    fn first_elem(&self) -> Option<Self::Out> {
        self.chars().next()
    }
}

impl<T: FirstElem> FirstElem for [T] {
    type Out = T::Out;

    fn first_elem(&self) -> Option<Self::Out> {
        self.first().and_then(T::first_elem)
    }
}

impl<T: FirstElem, const N: usize> FirstElem for [T; N] {
    type Out = T::Out;

    fn first_elem(&self) -> Option<Self::Out> {
        self.first().and_then(T::first_elem)
    }
}

/// Call [`MatchOne::is_match_one`]
///
/// Match `'-'` Please write at the beginning or end, e.g `"a-z-"`
///
/// # Examples
///
/// ```
/// # use char_classes::any;
/// assert!(any("ab",       'a'));
/// assert!(any("ab",       'b'));
/// assert!(any("a-c",      'a'));
/// assert!(any("a-c",      'b'));
/// assert!(any("a-ce-f",   'e'));
/// assert!(any("a-ce-",    '-'));
/// assert!(any("a-ce-",    'e'));
/// assert!(any("a-c",      Some('b')));
/// assert!(any("a-c",      ['b', 'd']));
/// assert!(any("a-c",      "bd"));
///
/// assert!(! any("a-c",    '-'));
/// assert!(! any("a-ce-",  'f'));
///
/// assert!(! any("a-c",    None::<char>));
/// assert!(! any("a-c",    ['d', 'b']));
/// assert!(! any("a-c",    "db"));
/// ```
pub fn any<T>(pattern: impl AsRef<T::Pattern>, val: T) -> bool
where T: MatchOne,
{
    val.is_match_one(pattern.as_ref())
}

fn match_impl<I>(pattern: I, val: &I::Item) -> bool
where I: IntoIterator,
      I::Item: PartialOrd + From<u8> + Copy,
{
    let pat = &mut pattern.into_iter();
    let dash = &I::Item::from(b'-');

    let Some(mut first) = pat.next() else {
        return false;
    };

    while let Some(ref cur) = pat.next() {
        if first == *val {
            return true;
        }
        if cur != dash {
            first = *cur;
        } else if let Some(to) = pat.next() {
            if (first..=to).contains(val) {
                return true;
            }
            if let Some(next) = pat.next() {
                first = next;
            } else {
                return false;
            }
        } else {
            first = *cur;
        }
    }

    first == *val
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_pattern() {
        let datas = [
            ("a", 'a'),
            ("ab", 'a'),
            ("ba", 'a'),
            ("bac", 'a'),
            ("bca", 'a'),
            ("a-e", 'c'),
            ("a-c", 'c'),
            ("a-bc", 'c'),
            ("a-bc", 'a'),
            ("a-bc", 'b'),
            ("你好", '你'),
            ("你好", '好'),
            ("a-", 'a'),
            ("a-", '-'),
            ("-a", '-'),
            ("-", '-'),
        ];

        for (pat, val) in datas {
            assert!(match_impl(pat.chars(), &val), "{pat:?}, {val:?}");
        }
    }

    #[test]
    fn basic_not_pattern() {
        let datas = [
            ("", 'a'),
            ("a-b", '-'),
            ("a-", 'c'),
            ("a-", 'b'),
        ];

        for (pat, val) in datas {
            assert!(! match_impl(pat.chars(), &val), "{pat:?}, {val:?}");
        }
    }

    #[test]
    fn first_pattern() {
        let datas = [
            ("a", "a"),
            ("你", "你好"),
            ("a-c", "a"),
            ("a-c", "b"),
        ];

        for (pat, val) in datas {
            assert!(any(pat, val));
        }
    }

    #[test]
    fn first_not_pattern_rest() {
        let datas = [
            ("a", "da"),
            ("好", "你好"),
            ("a-c", "da"),
            ("a-c", "db"),
            ("ab", "db"),
        ];

        for (pat, val) in datas {
            assert!(! any(pat, val));
        }
    }

    #[test]
    fn first_not_pattern_empty() {
        let datas = [
            ("a", ""),
            ("a-c", ""),
        ];

        for (pat, val) in datas {
            assert!(! any(pat, val));
        }
    }

    #[test]
    fn dash_range() {
        let datas = [
            ("+--", "+"),
            ("+--", ","),
            ("+--", "-"),
            ("+--a", "+"),
            ("+--a", ","),
            ("+--a", "-"),
            ("+--a", "a"),
            ("--0", "-"),
            ("--0", "."),
            ("--0", "/"),
            ("--0", "0"),
            ("--0a", "-"),
            ("--0a", "."),
            ("--0a", "/"),
            ("--0a", "0"),
            ("--0a", "a"),
            ("a-c-e-g", "a"),
            ("a-c-e-g", "b"),
            ("a-c-e-g", "c"),
            ("a-c-e-g", "e"),
            ("a-c-e-g", "f"),
            ("a-c-e-g", "g"),
            ("a-c-e-g", "-"),
        ];

        for (pat, val) in datas {
            assert!(any(pat, val), "{pat:?} cannot pattern {val:?}");
        }
    }

    #[test]
    fn dash_range_not_pat() {
        let datas = [
            ("+--a", "0"),
            ("---a", "0"),
            ("a-c-e-g", "d"),
        ];

        for (pat, val) in datas {
            assert!(! any(pat, val));
        }
    }
}
