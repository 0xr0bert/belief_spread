//! This module contains various errors that may be produced.
use thiserror::Error;
use uuid::Uuid;

use crate::SimTime;

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

/// An error for [`crate::update_activation_for_agent`].
#[derive(Error, Debug, PartialEq, Eq)]
pub enum UpdateActivationError {
    /// When the activation for a [`crate::Belief`] identified by [Uuid] at a [SimTime] is [None].
    #[error("Get activation is none")]
    GetActivationNone { time: SimTime, belief: Uuid },

    /// When the delta for a [`crate::Belief`] identified by [Uuid] is [None].
    #[error("Get delta is none")]
    GetDeltaNone { belief: Uuid },
}
