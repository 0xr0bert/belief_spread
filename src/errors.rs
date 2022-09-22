//! This module contains various errors that may be produced.
use thiserror::Error;

/// An error for when a supplied value is out of range.
#[derive(Error, Debug, PartialEq)]
pub enum OutOfRangeError {
    /// When a value is too low.
    #[error("value too low (found {found:?}, range [{min:?}, {max:?}])")]
    TooLow { found: f64, min: f64, max: f64 },
    /// When a value is too high.
    #[error("value too high (found {found:?}, range [{min:?}, {max:?}])")]
    TooHigh { found: f64, min: f64, max: f64 },
}
