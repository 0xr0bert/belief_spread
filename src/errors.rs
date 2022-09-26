//! This module contains various errors that may be produced.
use thiserror::Error;

use crate::{Belief, SimTime};

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

/// An error for [`Agent::update_activation`].
#[derive(Error, Debug, PartialEq)]
pub enum UpdateActivationError {
    /// When the activation for a [Belief] at a [SimTime] is [None].
    #[error("Get activation is none")]
    GetActivationNone {
        time: SimTime,
        belief: *const dyn Belief,
    },

    /// When the delta for a [Belief] is [None].
    #[error("Get delta is none")]
    GetDeltaNone { belief: *const dyn Belief },
}
