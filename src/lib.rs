#![no_std]
#![doc = include_str!("../README.md")]

#[doc = include_str!("../README.md")]
pub trait MatchOne {
    type Out;
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

    /// Call [`.match_one(pattern).is_some()`](#method.match_one)
    fn is_match_one(&self, pattern: &Self::Pattern) -> bool {
        self.match_one(pattern).is_some()
    }
}

impl<T: MatchOne> MatchOne for Option<T> {
    type Out = T::Out;
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.as_ref().and_then(|val| val.match_one(pattern))
    }
}

impl<T: MatchOne + ?Sized> MatchOne for &T {
    type Out = T::Out;
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        (**self).match_one(pattern)
    }
}

impl<T: MatchOne + ?Sized> MatchOne for &mut T {
    type Out = T::Out;
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        (**self).match_one(pattern)
    }
}

impl MatchOne for char {
    type Out = char;
    type Pattern = str;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        match_impl(pattern.chars(), self).then_some(*self)
    }
}

impl MatchOne for u8 {
    type Out = u8;
    type Pattern = [u8];

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        match_impl(pattern.iter().copied(), self).then_some(*self)
    }
}

impl MatchOne for str {
    type Out = char;
    type Pattern = str;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.chars().next().match_one(pattern)
    }
}

impl MatchOne for () {
    type Out = core::convert::Infallible;
    type Pattern = ();

    fn match_one(&self, _pattern: &Self::Pattern) -> Option<Self::Out> {
        None
    }
}

impl<T: MatchOne> MatchOne for [T] {
    type Out = T::Out;
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.first().match_one(pattern)
    }
}

impl<T: MatchOne, const N: usize> MatchOne for [T; N] {
    type Out = T::Out;
    type Pattern = T::Pattern;

    fn match_one(&self, pattern: &Self::Pattern) -> Option<Self::Out> {
        self.first().match_one(pattern)
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
    let pat = &mut pattern.into_iter().peekable();
    let dash = &I::Item::from(b'-');

    let Some(mut first) = pat.next() else {
        return false;
    };

    if first == *val {
        return true;
    }

    while let Some(ref cur) = pat.next() {
        let peek = pat.peek();

        if cur == dash && peek
            .is_some_and(|peek| {
                (first..=*peek).contains(val)
            })
        || cur == val && peek.is_none_or(|_| cur != dash)
        {
            return true;
        }

        first = *cur;
    }

    false
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
}
