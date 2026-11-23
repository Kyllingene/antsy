//! See [AnsiStr].
#![forbid(unsafe_code)]
#![warn(missing_docs)]
#![cfg_attr(not(test), no_std)]

use core::fmt;
use core::ops::Deref;

/// A helper trait for performing ANSI-escape-code-aware operations on strings.
pub trait AnsiStr: AsRef<str> {
    /// Returns the number of bytes that are part of an escape sequence.
    ///
    /// Consider caching this value if you need it more than once: calculating
    /// requires running through each escape again.
    fn escapes_len(&self) -> usize {
        self.segments().escapes().map(|e| e.raw.len()).sum()
    }

    /// Returns the number of bytes that aren't part of an escape sequence.
    ///
    /// Consider caching this value if you need it more than once: calculating
    /// requires running through each escape again.
    fn plain_len(&self) -> usize {
        self.as_ref().len() - self.escapes_len()
    }

    /// Iterate over each [segment](Segment) of the string.
    ///
    /// See [`FilteredSegments`] for info on filtering, printing, etc.
    fn segments(&self) -> Segments<'_> {
        Segments::new(self.as_ref(), All)
    }
}

impl<S: AsRef<str>> AnsiStr for S {}

/// A segment of an ANSI string.
///
/// Can be parsed out of a string via [`AnsiStr::segments`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Segment<'s> {
    /// A section of a string that has no escape codes.
    Plain(&'s str),
    /// An escape code within a string.
    Escape(Escape<'s>),
}

impl fmt::Debug for Segment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain(s) |
            Self::Escape(Escape { raw: s, .. }) => write!(f, "{s:?}"),
        }
    }
}

impl fmt::Display for Segment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain(s) |
            Self::Escape(Escape { raw: s, .. }) => f.write_str(s),
        }
    }
}

/// A method for filtering out [`Segment`]s from a [`FilteredSegments`] iterator.
///
/// Note that, due to how [`FilteredSegments`] and [`StringLikeDebug`] interact,
/// debug formatting a [`FilteredSegments`] with a custom filter, where `Output`
/// implements `Deref<Target = str>` but has a custom `Debug` impl (such as
/// `Cow<str>`), can lead to messy output.
pub trait Filter {
    /// The output type of the filter, to allow transformations.
    type Output<'s>;

    /// Apply the filter; return `None` to skip an item.
    fn apply<'s>(&mut self, item: Segment<'s>) -> Option<Self::Output<'s>>;
}

/// Do not perform any filtering on the segments.
#[derive(Clone)]
pub struct All;
/// Filter the segments to only escape sequences.
#[derive(Clone)]
pub struct Escapes;
/// Filter the segments to only non-escape-sequences.
#[derive(Clone)]
pub struct Plain;

impl Filter for All {
    type Output<'s> = Segment<'s>;

    fn apply<'s>(&mut self, item: Segment<'s>) -> Option<Self::Output<'s>> { Some(item) }
}

impl Filter for Escapes {
    type Output<'s> = Escape<'s>;

    fn apply<'s>(&mut self, item: Segment<'s>) -> Option<Self::Output<'s>> {
        if let Segment::Escape(escape) = item {
            Some(escape)
        } else {
            None
        }
    }
}

impl Filter for Plain {
    type Output<'s> = &'s str;

    fn apply<'s>(&mut self, item: Segment<'s>) -> Option<Self::Output<'s>> {
        if let Segment::Plain(plain) = item {
            Some(plain)
        } else {
            None
        }
    }
}

impl Filter for EscapeKind {
    type Output<'s> = &'s str;

    fn apply<'s>(&mut self, item: Segment<'s>) -> Option<Self::Output<'s>> {
        if let Segment::Escape(Escape { kind, raw }) = item && kind == *self {
            Some(raw)
        } else {
            None
        }
    }
}

impl<T, F> Filter for F
where
    F: for<'s> FnMut(Segment<'s>) -> Option<T>,
{
    type Output<'s> = T;

    fn apply<'s>(&mut self, item: Segment<'s>) -> Option<Self::Output<'s>> {
        self(item)
    }
}

/// An iterator over segments of an [`AnsiStr`].
///
/// You can use [`escapes`](FilteredSegments::escapes) and
/// [`plain`](FilteredSegments::plain) to quickly filter.
///
/// This type implements `Debug` and `Display`. When printed, it will print each
/// filtered item. You can use this to print only text/only escapes from a string.
#[derive(Clone)]
pub struct FilteredSegments<'s, F> {
    inner: &'s str,
    filter: F,

    next_escape: Option<Escape<'s>>,
}

/// An alias for an unfiltered [`FilteredSegments`].
pub type Segments<'s> = FilteredSegments<'s, All>;

impl<'s, F> FilteredSegments<'s, F> {
    /// Create a new iterator over the segments of string.
    pub fn new(string: &'s str, filter: F) -> Self {
        Self { inner: string, filter, next_escape: None, }
    }

    /// Modify the filter to [`All`].
    pub fn all(self) -> FilteredSegments<'s, All> {
        let Self { inner, next_escape, .. } = self;
        FilteredSegments { inner, filter: All, next_escape }
    }

    /// Modify the filter to [`Escapes`].
    pub fn escapes(self) -> FilteredSegments<'s, Escapes> {
        let Self { inner, next_escape, .. } = self;
        FilteredSegments { inner, filter: Escapes, next_escape }
    }

    /// Modify the filter to [`Plain`].
    pub fn plain(self) -> FilteredSegments<'s, Plain> {
        let Self { inner, next_escape, .. } = self;
        FilteredSegments { inner, filter: Plain, next_escape }
    }

    /// Use a custom filter on the segments.
    pub fn filter<NF>(self, filter: NF) -> FilteredSegments<'s, NF> {
        let Self { inner, next_escape, .. } = self;
        FilteredSegments { inner, filter, next_escape }
    }
}

impl<'s, F: Filter> Iterator for FilteredSegments<'s, F> {
    type Item = F::Output<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(item) = self.next_escape.take().and_then(|e| self.filter.apply(Segment::Escape(e))) {
                return Some(item);
            }

            if self.inner.is_empty() {
                return None;
            }

            let mut search = 0;
            let (pos, escape, rest) = loop {
                let Some(rel) = self.inner[search..].find('\x1b') else {
                    return self.filter.apply(Segment::Plain(core::mem::take(&mut self.inner)));
                };
                let pos = search + rel;
                match Escape::parse_from(&self.inner[pos..]) {
                    Some((escape, rest)) => break (pos, escape, rest),
                    None => search = pos + 1,
                }
            };

            let plain = &self.inner[..pos];
            self.inner = rest;
            if plain.is_empty() {
                if let Some(item) = self.filter.apply(Segment::Escape(escape)) {
                    return Some(item);
                }
            } else {
                self.next_escape = Some(escape);
                if let Some(item) = self.filter.apply(Segment::Plain(plain)) {
                    return Some(item);
                }
            }
        }
    }
}

impl<'s, F: Clone + Filter<Output<'s>: StringLikeDebug>> fmt::Debug for FilteredSegments<'s, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_no_quotes(self.clone(), f)
    }
}

impl<'s, F: Clone + Filter<Output<'s>: fmt::Display>> fmt::Display for FilteredSegments<'s, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for item in self.clone() {
            item.fmt(f)?;
        }
        Ok(())
    }
}

/// An escape sequence parsed out of a string.
///
/// A few things to note:
///  - Intervening C0 escapes are not permitted, for the sake of heapless parsing.
///    This restriction does not apply to ST-terminated payloads.
///  - C1 bytes (`0x9X`) are not valid UTF-8, and are thus not parsed.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Escape<'s> {
    /// The kind of escape.
    ///
    /// Different kinds of escapes have different syntaxes, that are
    /// parsed differently.
    pub kind: EscapeKind,

    /// The raw escape string.
    pub raw: &'s str,
}

impl fmt::Debug for Escape<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.raw)
    }
}

impl fmt::Display for Escape<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.raw)
    }
}

impl Deref for Escape<'_> {
    type Target = str;

    fn deref(&self) -> &str {
        self.raw
    }
}

impl<'s> Escape<'s> {
    fn parse_from(s: &'s str) -> Option<(Self, &'s str)> {
        let esc = s.strip_prefix('\x1b')?;

        let parsers: [(fn(_) -> _, _); _] = [
            (parse_csi, EscapeKind::Csi),
            (parse_string_st, EscapeKind::St(StEscape::String)),
            (parse_dcs, EscapeKind::St(StEscape::Dcs)),
            (parse_osc, EscapeKind::St(StEscape::Osc)),
            (parse_fe, EscapeKind::Fe),
        ];

        for (parser, kind) in parsers {
            if let Some(split) = parser(esc) {
                let (escape, rest) = s.split_at(split + 1);
                return Some((Self { kind, raw: escape }, rest));
            }
        }

        None
    }
}

/// The kind of an [`Escape`].
///
/// Different kinds of escapes have different syntaxes, that are
/// parsed differently.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EscapeKind {
    /// An FE escape (e.g. `ESC N`).
    Fe,

    /// A CSI escape (e.g. `ESC [0m`).
    Csi,

    /// An [ST escape](StEscape).
    St(StEscape),
}

/// An escape sequence terminated by ST (`ESC \`).
///
/// Note that while the standard also allows for terminating with the single
/// byte `0x9C`, that is invalid UTF-8 and is therefore impossible to properly
/// represent in Rust.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StEscape {
    /// A DCS escape.
    ///
    /// The shape is effectively a CSI escape, with a tweaked header and a
    /// string payload following.
    Dcs,

    /// An SOS, PM, or APC escape.
    ///
    /// An almost-arbitrary string of bytes until the terminator.
    String,

    /// An OSC escape.
    ///
    /// These can also be terminated by BEL.
    Osc,
}

fn parse_fe(s: &str) -> Option<usize> {
    let reserved = ['[', ']', 'P', 'X', '^', '_'];
    let inter = (0x20 as char)..=(0x2F as char);
    let fin = (0x30 as char)..=(0x7E as char);

    if reserved.contains(&s.chars().next()?) {
        return None;
    }

    let head = s.find(|ch| !inter.contains(&ch))?;
    s.chars().nth(head).is_some_and(|ch| fin.contains(&ch)).then_some(
        head + 1
    )
}

fn parse_csi(s: &str) -> Option<usize> {
    let param = (0x30 as char)..=(0x3F as char);
    let inter = (0x20 as char)..=(0x2F as char);
    let fin = (0x40 as char)..=(0x7E as char);

    if s.len() < 2 || !s.starts_with('[') {
        return None;
    }

    let params = s[1..].find(|ch| !param.contains(&ch))? + 1;
    let inters = s[params..].find(|ch| !inter.contains(&ch))? + params;
    s.chars().nth(inters).is_some_and(|ch| fin.contains(&ch)).then_some(
        inters + 1
    )
}

const ABORT: [char; 2] = ['\x18', '\x1A'];

fn parse_dcs(s: &str) -> Option<usize> {
    let param = (0x30 as char)..=(0x3F as char);
    let inter = (0x20 as char)..=(0x2F as char);
    let fin = (0x40 as char)..=(0x7E as char);

    if s.len() < 3 || !s.starts_with('P') {
        return None;
    }

    let params = s[1..].find(|ch| !param.contains(&ch))? + 1;
    let inters = s[params..].find(|ch| !inter.contains(&ch))? + params;

    if !fin.contains(&s.chars().nth(inters)?) {
        return None;
    }

    let rest = &s[(inters + 1)..];
    let end = rest.find("\x1b\\")? + inters + 3;

    if s[..end].contains(ABORT) {
        return None;
    }

    Some(end)
}

fn parse_string_st(s: &str) -> Option<usize> {
    let cmd = ['X', '^', '_'];

    if s.len() < 3 || !s.starts_with(cmd) {
        return None;
    }

    let end = s.find("\x1b\\")? + 2;

    if s[..end].contains(ABORT) {
        return None;
    }

    Some(end)
}

fn parse_osc(s: &str) -> Option<usize> {
    if !s.starts_with(']') {
        return None;
    }

    let st = s.find("\x1b\\").map(|i| i + 1);
    let bel = s.find('\x07');

    let end = match (st, bel) {
        (Some(st), Some(bel)) => st.min(bel),
        (Some(st), None) => st,
        (None, Some(bel)) => bel,
        (None, None) => return None,
    } + 1;

    if s[..end].contains(ABORT) {
        return None;
    }

    Some(end)
}

/// A type whose `Debug` impl produces `Formatter` calls like `str` does.
pub trait StringLikeDebug: fmt::Debug + sealed::Sealed {}
impl<T> StringLikeDebug for T where T: fmt::Debug + sealed::Sealed {}
mod sealed {
    pub trait Sealed {}

    // Reasonable enough assumption
    impl<T> Sealed for T where T: core::ops::Deref<Target = str> {}

    impl Sealed for super::Segment<'_> {}
}

/// Prints a series of strings in debug form, but without the opening/closing quotes.
fn debug_no_quotes<I: IntoIterator<Item: fmt::Debug>>(
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

    f.write_char('"')?;
    let mut w = DebugNoQuotes(f);
    for s in i {
        write!(&mut w, "{s:?}")?;
    }
    f.write_char('"')
}

#[cfg(test)]
mod test {
    use pretty_assertions::assert_eq;

    use crate::{AnsiStr, Escape, EscapeKind, StEscape};

    const FE_GOOD: &str = "$#%,mabc";
    const CSI_GOOD: &str = "[38;5;1 /!mabc";
    const DCS_GOOD: &str = "P38;5;1 /!m\x1b a1:/\\ \x1b\\abc";
    const STRING_ST_GOOD: &str = "X!3 /m\x1b \\a\x1b\\abc";
    const OSC_GOOD: &str = "]38;5;1 /!m\x1b a1:/\\ \x07abc";

    #[test]
    fn parse_fe() {
        assert_eq!(crate::parse_fe(FE_GOOD), Some(5));

        let bad = ["!", "\n!m", ""];
        for bad in bad {
            assert_eq!(crate::parse_fe(bad), None);
        }
    }

    #[test]
    fn parse_csi() {
        assert_eq!(crate::parse_csi(CSI_GOOD), Some(11));

        let bad = ["[38;5;1 /!", "[ 3m"];
        for bad in bad {
            assert_eq!(crate::parse_csi(bad), None);
        }
    }

    #[test]
    fn parse_dcs() {
        assert_eq!(crate::parse_dcs(DCS_GOOD), Some(21));

        let bad = ["]/3m\x1b\\", "]", "]38;5;1 /!m", "]38;5;1\x18 /!m\x1b a1:/\\ \x1b\\abc"];
        for bad in bad {
            assert_eq!(crate::parse_dcs(bad), None);
        }
    }

    #[test]
    fn parse_string_st() {
        assert_eq!(crate::parse_string_st(STRING_ST_GOOD), Some(12));

        let bad = ["]A \x1b\\", "]", "]^", "]X38;5;1\x18 /!m\x1b a1:/\\ \x1b\\abc"];
        for bad in bad {
            assert_eq!(crate::parse_string_st(bad), None);
        }
    }

    #[test]
    fn parse_osc() {
        assert_eq!(crate::parse_osc(OSC_GOOD), Some(20));

        let bad = ["]", "]abc", "]38;5;1\x18 /!m\x1b a1:/\\ \x07abc"];
        for bad in bad {
            assert_eq!(crate::parse_osc(bad), None);
        }
    }

    #[test]
    fn parse_escape() {
        let good = [
            (FE_GOOD, EscapeKind::Fe),
            (CSI_GOOD, EscapeKind::Csi),
            (DCS_GOOD, EscapeKind::St(StEscape::Dcs)),
            (STRING_ST_GOOD, EscapeKind::St(StEscape::String)),
            (OSC_GOOD, EscapeKind::St(StEscape::Osc)),
        ];

        for (good, kind) in good {
            let good = format!("\x1b{good}");
            assert_eq!(Escape::parse_from(&good).map(|(e, _)| e.kind), Some(kind));
        }
    }

    #[test]
    fn segments() {
        use crate::Segment;

        let s = "abc\x1b[38;5;1mdef\x1b]def\x1b\\ghi\x1bJjkl";
        let segments = s.segments().collect::<Vec<_>>();

        assert_eq!(segments, [
            Segment::Plain("abc"),
            Segment::Escape(Escape { raw: "\x1b[38;5;1m", kind: EscapeKind::Csi }),
            Segment::Plain("def"),
            Segment::Escape(Escape { raw: "\x1b]def\x1b\\", kind: EscapeKind::St(StEscape::Osc) }),
            Segment::Plain("ghi"),
            Segment::Escape(Escape { raw: "\x1bJ", kind: EscapeKind::Fe }),
            Segment::Plain("jkl"),
        ]);

        assert_eq!(s.segments().to_string(), s);
        assert_eq!(s.segments().escapes().to_string(), "\x1b[38;5;1m\x1b]def\x1b\\\x1bJ");
        assert_eq!(s.segments().plain().to_string(), "abcdefghijkl");
        assert_eq!(format!("{:?}", s.segments()), r#""abc\u{1b}[38;5;1mdef\u{1b}]def\u{1b}\\ghi\u{1b}Jjkl""#);

        assert_eq!("\x1b\n".segments().to_string(), "\x1b\n");
    }
}
