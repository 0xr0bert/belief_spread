//! A library for modelling how beliefs spread through social networks.
mod agent;
mod behaviour;
mod belief;
pub mod errors;
mod named;
mod uuidd;

pub use crate::agent::{Agent, BasicAgent};
pub use crate::behaviour::{BasicBehaviour, Behaviour, BehaviourPtr};
pub use crate::belief::{BasicBelief, Belief, BeliefPtr};
pub use crate::named::Named;
pub use crate::uuidd::UUIDd;

/// The simulation time.
pub type SimTime = u32;
