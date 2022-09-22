use uuid::Uuid;

use crate::UUIDd;

/// An [Agent] which may exist in the model.
pub trait Agent: UUIDd {}

/// A [BasicAgent] is an implementation of [Agent].
pub struct BasicAgent {
    uuid: Uuid,
}

impl BasicAgent {
    /// Create a new [BasicAgent] with a random [Uuid]
    ///
    /// # Returns
    /// The new [BasicAgent] with a [Uuid] generated using
    /// [`uuid::Uuid::new_v4`].
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::BasicAgent;
    ///
    /// let a = BasicAgent::new();
    /// ```
    pub fn new() -> Self {
        Self::new_with_uuid(Uuid::new_v4())
    }

    /// Create a new [BasicAgent] with a specified [Uuid]
    ///
    /// # Arguments
    /// - `uuid`: The [Uuid] of the [BasicAgent].
    ///
    /// # Returns
    /// The new [BasicAgent] with a specified [Uuid].
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::BasicAgent;
    /// use uuid::Uuid;
    ///
    /// let u = Uuid::new_v4();
    /// let a = BasicAgent::new_with_uuid(u);
    /// ```
    pub fn new_with_uuid(u: Uuid) -> Self {
        BasicAgent { uuid: u }
    }
}

impl Agent for BasicAgent {}

impl UUIDd for BasicAgent {
    /// Get the UUID of the [BasicAgent].
    fn uuid(&self) -> &Uuid {
        &self.uuid
    }

    /// Set the UUID of the [BasicAgent].
    fn set_uuid(&mut self, u: Uuid) {
        self.uuid = u;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_assigns_random_uuid() {
        let a1 = BasicAgent::new();
        let a2 = BasicAgent::new();
        assert_ne!(a1.uuid, a2.uuid);
    }

    #[test]
    fn new_with_uuid_assigns_uuid() {
        let u = Uuid::new_v4();
        let a = BasicAgent::new_with_uuid(u.clone());
        assert_eq!(a.uuid, u)
    }

    #[test]
    fn uuid_returns_uuid() {
        let u = Uuid::new_v4();
        let a = BasicAgent::new_with_uuid(u.clone());
        assert_eq!(a.uuid(), &u)
    }

    #[test]
    fn set_uuid_sets_uuid() {
        let mut a = BasicAgent::new();
        let u = Uuid::new_v4();
        a.set_uuid(u.clone());
        assert_eq!(a.uuid, u)
    }
}
