use std::fmt::Display;
use std::ops::{Bound, RangeBounds};

pub mod prelude {
    pub use crate::{AnsiStr, AnsiString};
}

/// A segment of an [`AnsiStr`].
///
/// Can either be an escape sequence or a normal string.
#[derive(Debug, Clone, PartialEq)]
pub enum AnsiStrSegment<'a> {
    Escape(&'a str),
    Normal(&'a str),
}

impl<'a> AnsiStrSegment<'a> {
    /// Returns the length of the segment, regardless of type.
    pub fn len(&self) -> usize {
        match self {
            Self::Escape(s) | Self::Normal(s) => s.len(),
        }
    }

    /// Returns whether or not the segment is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// A segment of an [`AnsiString`].
///
/// Can either be an escape sequence or a normal string.
#[derive(Debug, Clone, PartialEq)]
pub enum AnsiStringSegment {
    Escape(String),
    Normal(String),
}

impl AnsiStringSegment {
    /// Returns the length of the segment, regardless of type.
    pub fn len(&self) -> usize {
        match self {
            Self::Escape(s) | Self::Normal(s) => s.len(),
        }
    }

    /// Returns whether or not the segment is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AnsiStr<'a>(Vec<AnsiStrSegment<'a>>, &'a str);

impl<'a> AnsiStr<'a> {
    pub fn new(s: &'a str) -> Self {
        let mut string = Vec::new();

        let mut in_escape = false;
        let mut escape = 0..0;
        let mut normal = 0..0;
        for (i, ch) in s.chars().enumerate() {
            if !in_escape && ch == '\x1b' {
                if !normal.is_empty() {
                    string.push(AnsiStrSegment::Normal(&s[normal.clone()]));
                    normal.end = normal.start;
                }

                in_escape = true;
                escape.start = i;
                escape.end = i + 1;
            } else if in_escape && escape.len() == 1 {
                if ch == '[' {
                    escape.end += 1;
                } else {
                    in_escape = false;
                    normal.end = escape.end + 1;
                    escape = 0..0;
                }
            } else if in_escape && ch == 'm' {
                escape.end += 1;
                string.push(AnsiStrSegment::Escape(&s[escape.clone()]));
                escape = 0..0;
                in_escape = false;
                normal = i + 1..i + 1;
            } else if in_escape {
                escape.end += 1;
            } else {
                normal.end += 1;
            }
        }

        Self(string, s)
    }

    /// Returns a String equivalent to a slice of the string.
    /// While the indices ignore escapes, the resulting
    /// string includes them.
    ///
    /// # Panics
    ///
    /// Panics if the indices are out-of-bounds of the normal
    /// segments of the string.
    pub fn get(&self, idx: impl RangeBounds<usize>) -> String {
        let mut res = String::new();

        let (start, end) = self.bounds_to_idx(idx.start_bound(), idx.end_bound());
        let length = end - start;
        let mut si = start;

        let mut needed = length;
        for segment in &self.0 {
            match segment {
                AnsiStrSegment::Escape(s) => res.push_str(s),
                AnsiStrSegment::Normal(s) => {
                    if si >= s.len() {
                        si -= s.len();
                        continue;
                    }

                    if needed >= s.len() - si {
                        res.push_str(&s[si..]);
                        needed -= s.len() - si;
                        si = 0;
                    } else {
                        res.push_str(&s[si..needed]);
                        needed = 0;
                        break;
                    }
                }
            }
        }

        if needed != 0 {
            panic!("bounds out of range of AnsiStr: {start}..{end}");
        }

        res
    }

    /// Returns the length, excluding escapes.
    pub fn len(&self) -> usize {
        self.0.iter().fold(0, |l, s| {
            if let AnsiStrSegment::Normal(s) = s {
                l + s.len()
            } else {
                l
            }
        })
    }

    /// Returns the length, including escapes.
    pub fn ansi_len(&self) -> usize {
        self.0.iter().fold(0, |l, s| l + s.len())
    }

    /// Returns true if the string is empty.
    ///
    /// Ignores escapes.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty() || self.len() == 0
    }

    /// Returns a reference to the original string.
    pub fn as_str(&self) -> &'a str {
        self.1
    }

    /// Transforms a [`Bound`] to indices.
    fn bounds_to_idx(&self, start: Bound<&usize>, end: Bound<&usize>) -> (usize, usize) {
        (
            match start {
                Bound::Unbounded => 0,
                Bound::Included(t) => *t,
                Bound::Excluded(t) => *t + 1,
            },
            match end {
                Bound::Unbounded => self.len(),
                Bound::Included(t) => *t + 1,
                Bound::Excluded(t) => *t,
            },
        )
    }
}

impl<'a> Display for AnsiStr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for segment in &self.0 {
            match segment {
                AnsiStrSegment::Escape(s) | AnsiStrSegment::Normal(s) => write!(f, "{s}")?,
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AnsiString(Vec<AnsiStringSegment>, String);

impl AnsiString {
    pub fn new(s: String) -> Self {
        let mut string = Vec::new();

        let mut in_escape = false;
        let mut escape = 0..0;
        let mut normal = 0..0;
        for (i, ch) in s.chars().enumerate() {
            if !in_escape && ch == '\x1b' {
                if !normal.is_empty() {
                    string.push(AnsiStringSegment::Normal(s[normal.clone()].to_string()));
                    normal.end = normal.start;
                }

                in_escape = true;
                escape.start = i;
                escape.end = i + 1;
            } else if in_escape && escape.len() == 1 {
                if ch == '[' {
                    escape.end += 1;
                } else {
                    in_escape = false;
                    normal.end = escape.end + 1;
                    escape = 0..0;
                }
            } else if in_escape && ch == 'm' {
                escape.end += 1;
                string.push(AnsiStringSegment::Escape(s[escape.clone()].to_string()));
                escape = 0..0;
                in_escape = false;
                normal = i + 1..i + 1;
            } else if in_escape {
                escape.end += 1;
            } else {
                normal.end += 1;
            }
        }

        Self(string, s)
    }

    /// Returns a String equivalent to a slice of the string.
    /// While the indices ignore escapes, the resulting
    /// string includes them.
    ///
    /// # Panics
    ///
    /// Panics if the indices are out-of-bounds of the normal
    /// segments of the string.
    pub fn get(&self, idx: impl RangeBounds<usize>) -> String {
        let mut res = String::new();

        let (start, end) = self.bounds_to_idx(idx.start_bound(), idx.end_bound());
        let length = end - start;
        let mut si = start;

        let mut needed = length;
        for segment in &self.0 {
            match segment {
                AnsiStringSegment::Escape(s) => res.push_str(s),
                AnsiStringSegment::Normal(s) => {
                    if si >= s.len() {
                        si -= s.len();
                        continue;
                    }

                    if needed >= s.len() - si {
                        res.push_str(&s[si..]);
                        needed -= s.len() - si;
                        si = 0;
                    } else {
                        res.push_str(&s[si..needed]);
                        needed = 0;
                        break;
                    }
                }
            }
        }

        if needed != 0 {
            panic!("bounds out of range of AnsiString: {start}..{end}");
        }

        res
    }

    /// Returns the length, excluding escapes.
    pub fn len(&self) -> usize {
        self.0.iter().fold(0, |l, s| {
            if let AnsiStringSegment::Normal(s) = s {
                l + s.len()
            } else {
                l
            }
        })
    }

    /// Returns the length, including escapes.
    pub fn ansi_len(&self) -> usize {
        self.0.iter().fold(0, |l, s| l + s.len())
    }

    /// Returns true if the string is empty.
    ///
    /// Ignores escapes.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty() || self.len() == 0
    }

    /// Returns a reference to the original string.
    pub fn as_str(&self) -> &str {
        &self.1
    }

    /// Returns a copy of the original string.
    pub fn as_string(&self) -> String {
        self.1.clone()
    }

    /// Transforms a [`Bound`] to indices.
    fn bounds_to_idx(&self, start: Bound<&usize>, end: Bound<&usize>) -> (usize, usize) {
        (
            match start {
                Bound::Unbounded => 0,
                Bound::Included(t) => *t,
                Bound::Excluded(t) => *t + 1,
            },
            match end {
                Bound::Unbounded => self.len(),
                Bound::Included(t) => *t + 1,
                Bound::Excluded(t) => *t,
            },
        )
    }
}

impl Display for AnsiString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for segment in &self.0 {
            match segment {
                AnsiStringSegment::Escape(s) | AnsiStringSegment::Normal(s) => write!(f, "{s}")?,
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::*;

    const TEST_STRING: &str = "Hello, \x1b[0m\x1b[38;5;4mWorld!\x1b[0m";

    #[test]
    fn basic_test() {
        assert_eq!(
            AnsiStr::new(TEST_STRING),
            AnsiStr(
                vec![
                    AnsiStrSegment::Normal("Hello, "),
                    AnsiStrSegment::Escape("\u{1b}[0m"),
                    AnsiStrSegment::Escape("\u{1b}[38;5;4m"),
                    AnsiStrSegment::Normal("World!"),
                    AnsiStrSegment::Escape("\u{1b}[0m")
                ],
                TEST_STRING
            )
        );
    }

    #[test]
    fn length() {
        let s = AnsiStr::new(TEST_STRING);

        assert_eq!(s.len(), 13);
        assert_eq!(s.ansi_len(), TEST_STRING.len());
        assert!(!s.is_empty());
    }

    #[test]
    fn slice_from_start() {
        let s = AnsiStr::new(TEST_STRING);
        assert_eq!(s.get(0..5), "Hello");
    }

    #[test]
    fn slice_from_middle() {
        let s = AnsiStr::new(TEST_STRING);
        assert_eq!(s.get(2..8), "llo, \x1b[0m\x1b[38;5;4mW");
    }

    #[test]
    fn basic_owned() {
        assert_eq!(
            AnsiString::new(TEST_STRING.to_string()),
            AnsiString(
                vec![
                    AnsiStringSegment::Normal("Hello, ".to_string()),
                    AnsiStringSegment::Escape("\u{1b}[0m".to_string()),
                    AnsiStringSegment::Escape("\u{1b}[38;5;4m".to_string()),
                    AnsiStringSegment::Normal("World!".to_string()),
                    AnsiStringSegment::Escape("\u{1b}[0m".to_string())
                ],
                TEST_STRING.to_string()
            )
        );
    }

    #[test]
    fn owned_length() {
        let s = AnsiString::new(TEST_STRING.to_string());

        assert_eq!(s.len(), 13);
        assert_eq!(s.ansi_len(), TEST_STRING.len());
        assert!(!s.is_empty());
    }

    #[test]
    fn owned_slice_from_start() {
        let s = AnsiString::new(TEST_STRING.to_string());
        assert_eq!(s.get(0..5), "Hello");
    }

    #[test]
    fn owned_slice_from_middle() {
        let s = AnsiString::new(TEST_STRING.to_string());
        assert_eq!(s.get(2..8), "llo, \x1b[0m\x1b[38;5;4mW");
    }
}
