//! See [AnsiStr].
#![forbid(unsafe_code)]
#![warn(missing_docs)]

use std::fmt;
use std::iter;
use std::ops::{Bound, Deref, RangeInclusive};

/// A wrapper around a string that keeps track of ANSI escape codes.
#[derive(Clone)]
pub struct AnsiStr<S> {
    inner: S,
    escapes: Box<[RangeInclusive<usize>]>,
    escapes_len: usize,
}

/// Debug-prints the internal string without modifications.
///
/// See [AnsiStr::escapes] and [AnsiStr::plain] if you want different behavior.
impl<S: AsRef<str>> fmt::Debug for AnsiStr<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// Prints the internal string without modifications.
///
/// See [AnsiStr::escapes] and [AnsiStr::plain] if you want different behavior.
impl<S: AsRef<str>> fmt::Display for AnsiStr<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

/// Dereferences to the internal string without modifications.
impl<S: AsRef<str>> Deref for AnsiStr<S> {
    type Target = str;

    fn deref(&self) -> &str {
        self.inner.as_ref()
    }
}

/// Dereferences to the internal string without modifications.
impl<S: AsRef<str>> AsRef<str> for AnsiStr<S> {
    fn as_ref(&self) -> &str {
        self.inner.as_ref()
    }
}

impl<S: AsRef<str>> AnsiStr<S> {
    /// Create a new `AnsiStr`, calculating escape sequence boundaries up-front.
    pub fn new(string: S) -> Self {
        let mut this = Self {
            inner: string,
            escapes: Default::default(),
            escapes_len: 0,
        };
        this.recalculate();
        this
    }

    /// Get an iterator over the escapes in the string.
    ///
    /// Also implements `Debug`/`Display`.
    pub fn escapes(&self) -> AnsiEscapes<'_> {
        AnsiEscapes {
            inner: self,
            escapes: &self.escapes[..],
        }
    }

    /// Get an iterator over the non-escapes in the string.
    ///
    /// Also implements `Debug`/`Display`.
    pub fn plain(&self) -> AnsiPlain<'_> {
        AnsiPlain {
            inner: self,
            escapes: &self.escapes[..],
            cursor: 0,
        }
    }

    /// Returns the number of bytes that are part of an escape sequence.
    pub fn escapes_len(&self) -> usize {
        self.escapes_len
    }

    /// Returns the number of bytes that aren't part of an escape sequence.
    pub fn plain_len(&self) -> usize {
        self.len() - self.escapes_len
    }

    /// Modify the inner string, re-calculating the escape sequences.
    pub fn modify(&mut self, f: impl FnOnce(&mut S)) {
        f(&mut self.inner);
        self.recalculate();
    }

    /// Get a reference to the underlying string container.
    pub fn inner(&self) -> &S {
        &self.inner
    }

    /// Consume this `AnsiStr` and return the underyling string container.
    pub fn into_inner(self) -> S {
        self.inner
    }

    /// Recalculates `self.escapes_len` and `self.escapes` from scratch.
    fn recalculate(&mut self) {
        let s = self.inner.as_ref();

        self.escapes_len = 0;
        // use a sliding window to ensure an unterminated escape doesn't bleed into the next
        self.escapes = windows_trailing(self.inner.as_ref().match_indices("\x1b["))
            .flat_map(|((start, _), end)| {
                let end = start
                    + s[(
                        Bound::Included(start),
                        end.map(|(end, _)| Bound::Excluded(end))
                            .unwrap_or(Bound::Unbounded),
                    )]
                        .find('m')?;
                self.escapes_len += end - start + 1;
                Some(start..=end)
            })
            .collect();
    }
}

/// An iterator over the escape sequences in an [`AnsiStr`].
///
/// Create with [`AnsiStr::escapes`].
#[derive(Clone)]
pub struct AnsiEscapes<'src> {
    inner: &'src str,
    escapes: &'src [RangeInclusive<usize>],
}

/// Debug-prints the remaining escape sequences in the iterator.
impl fmt::Debug for AnsiEscapes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;
        f.write_char('"')?;
        debug_no_quotes(self.clone(), f)?;
        f.write_char('"')
    }
}

/// Prints the remaining escape sequences in the iterator.
impl fmt::Display for AnsiEscapes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for s in self.clone() {
            s.fmt(f)?;
        }
        Ok(())
    }
}

impl<'src> Iterator for AnsiEscapes<'src> {
    type Item = &'src str;

    fn next(&mut self) -> Option<&'src str> {
        Some(&self.inner[self.escapes.split_off_first()?.clone()])
    }
}

/// An iterator over the non-escapes in an [`AnsiStr`].
///
/// Create with [`AnsiStr::plain`].
#[derive(Clone)]
pub struct AnsiPlain<'src> {
    inner: &'src str,
    escapes: &'src [RangeInclusive<usize>],
    cursor: usize,
}

/// Debug-prints the remaining non-escapes in the iterator.
impl fmt::Debug for AnsiPlain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;
        f.write_char('"')?;
        debug_no_quotes(self.clone(), f)?;
        f.write_char('"')
    }
}

/// Prints the remaining non-escapes in the iterator.
impl fmt::Display for AnsiPlain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for s in self.clone() {
            s.fmt(f)?;
        }
        Ok(())
    }
}

impl<'src> Iterator for AnsiPlain<'src> {
    type Item = &'src str;

    fn next(&mut self) -> Option<&'src str> {
        loop {
            if self.inner.is_empty() {
                return None;
            }

            let s = if let Some(range) = self.escapes.split_off_first() {
                let (s, rest) = self.inner.split_at(*range.start() - self.cursor);
                self.cursor += s.len();

                let (escape, rest) = rest.split_at(*range.end() - self.cursor + 1);
                self.cursor += escape.len();

                self.inner = rest;

                s
            } else {
                std::mem::take(&mut self.inner)
            };

            if !s.is_empty() {
                return Some(s);
            }
        }
    }
}

/// Creates a sliding window over the sub-iterator; the last window is `(x, None)`.
fn windows_trailing<I: Iterator<Item: Clone>>(
    mut iter: I,
) -> impl Iterator<Item = (I::Item, Option<I::Item>)> {
    let mut next = iter.next();
    iter::from_fn(move || {
        let last = next.take()?;
        next = iter.next();

        Some((last, next.clone()))
    })
}

/// Prints a series of strings in debug form, but without the opening/closing quotes.
fn debug_no_quotes<'a, I: IntoIterator<Item = &'a str>>(
    i: I,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    use fmt::Write;

    struct DebugNoQuotes<'a, 'b>(&'a mut fmt::Formatter<'b>);

    impl Write for DebugNoQuotes<'_, '_> {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            if s == "\"" {
                Ok(())
            } else {
                self.0.write_str(s)
            }
        }
    }

    let mut w = DebugNoQuotes(f);
    for s in i {
        write!(&mut w, "{s:?}")?;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use crate::AnsiStr;

    const TEST: &str = "abc\x1b[38;5;1mdef\x1b[0mghi";

    #[test]
    fn lengths() {
        let s = AnsiStr::new(TEST);

        assert_eq!(s.len(), TEST.len());
        assert_eq!(s.escapes_len(), 9 + 4);
        assert_eq!(s.plain_len(), 3 * 3);
    }

    #[test]
    fn escapes_fmt() {
        let s = AnsiStr::new(TEST);
        let escapes = s.escapes().to_string();
        assert_eq!(escapes, "\x1b[38;5;1m\x1b[0m");
    }

    #[test]
    fn plain_fmt() {
        let s = AnsiStr::new(TEST);
        let plain = s.plain().to_string();
        assert_eq!(plain, "abcdefghi");
    }

    #[test]
    fn modify() {
        let mut s = AnsiStr::new(TEST.to_string());
        s.modify(|s| *s = s[2..13].to_string());

        let escapes = s.escapes().to_string();
        let plain = s.plain().to_string();

        assert_eq!(&*s, "c\x1b[38;5;1md");
        assert_eq!(escapes, "\x1b[38;5;1m");
        assert_eq!(plain, "cd");
    }
}
