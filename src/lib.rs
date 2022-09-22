mod agent;
mod behaviour;
mod belief;
pub mod errors;
mod named;
mod uuidd;

pub use crate::agent::Agent;
pub use crate::behaviour::{BasicBehaviour, Behaviour};
pub use crate::belief::{BasicBelief, Belief};
pub use crate::named::Named;
pub use crate::uuidd::UUIDd;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
