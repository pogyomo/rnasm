//! Provide a way to hold the range of source code.
//!
//! # `Span` and `Spannable`
//!
//! `Span` is a core of this crate. This struct hold the start offset of 
//! source code and the length of the item. You can concat two `Span`
//! using `+` operator, so you can easily calculate span of the item
//! which hold several `Spannable` items.
//!
//! `Spannable` is a helper trait to get `Span` of item in the same way.
//! Whether the item hold `Span` directly or not, you can get its
//! `Span` by calling `span` method if it implement `Spannable`.

use derive_new::new;
use std::ops::Add;

/// A trait for object who have its `Span`.
pub trait Spannable {
    fn span(&self) -> Span;
}

/// A struct which hold the range of source code where the item come from.
#[derive(new)]
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    offset: usize,
    len: usize,
}

impl Span {
    /// Return start offset of the item on the source code.
    ///
    /// # Examples
    ///
    /// ```
    /// use rnasm_span::Span;
    /// let span = Span::new(10, 20);
    /// assert_eq!(span.offset(), 10);
    /// ```
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Return the length of the item on the source code.
    ///
    /// # Examples
    ///
    /// ```
    /// use rnasm_span::Span;
    /// let span = Span::new(10, 20);
    /// assert_eq!(span.len(), 20);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }
}

impl Add for Span {
    type Output = Self;

    /// Concat two `Span` and return the `Span`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rnasm_span::Span;
    /// let lhs = Span::new(20, 31);
    /// let rhs = Span::new(50, 13);
    /// assert_eq!(lhs + rhs, Span::new(20, 43));
    /// assert_eq!(rhs + lhs, Span::new(20, 43));
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        if self.offset <= rhs.offset {
            if self.offset + self.len < rhs.offset + rhs.len {
                Self {
                    offset: self.offset,
                    len: rhs.offset - self.offset + rhs.len
                }
            } else {
                Self {
                    offset: self.offset,
                    len: self.len
                }
            }
        } else {
            rhs.add(self)
        }
    }
}
