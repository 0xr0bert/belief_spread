//! A library for modelling how beliefs spread through social networks.
mod agent;
mod behaviour;
mod belief;
pub mod errors;
mod named;
mod uuidd;

pub use crate::agent::{
    update_activation_for_agent, update_activation_for_all_beliefs_for_agent, Agent, BasicAgent,
};
pub use crate::behaviour::{BasicBehaviour, Behaviour};
pub use crate::belief::{BasicBelief, Belief};
pub use crate::named::Named;
pub use crate::uuidd::UUIDd;

/// The simulation time.
pub type SimTime = u32;
