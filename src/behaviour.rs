use by_address::ByAddress;
use core::fmt::Debug;
use std::{cell::RefCell, rc::Rc};
use uuid::Uuid;

use crate::{Named, UUIDd};

/// A Behaviour.
pub trait Behaviour: UUIDd + Named + Debug {}

/// A [Rc] [RefCell] pointer to [Behaviour] compared by address.
pub type BehaviourPtr = ByAddress<Rc<RefCell<dyn Behaviour>>>;

/// A BasicBehaviour is an implementation of a [Behaviour].
#[derive(Debug)]
pub struct BasicBehaviour {
    /// The name of the [BasicBehaviour]
    name: String,
    /// The [Uuid] of the [BasicBehaviour].
    uuid: Uuid,
}

impl BasicBehaviour {
    /// Create a new [BasicBehaviour] with random [Uuid].
    ///
    /// # Arguments
    /// - `name`: The name of the [BasicBehaviour].
    ///
    /// # Returns
    /// The new [BasicBehaviour] with a [Uuid] generated using
    /// [`uuid::Uuid::new_v4`].
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::BasicBehaviour;
    ///
    /// let b = BasicBehaviour::new("Behaviour 1".to_string());
    /// ```
    pub fn new(name: String) -> BasicBehaviour {
        Self::new_with_uuid(name, Uuid::new_v4())
    }

    /// Create a new [BasicBehaviour] with specified [Uuid].
    ///
    /// # Arguments
    /// - `name`: The name of the [BasicBehaviour].
    /// - `uuid`: The [Uuid] of the [BasicBehaviour].
    ///
    /// # Returns
    /// The new [BasicBehaviour].
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::BasicBehaviour;
    /// use uuid::Uuid;
    ///
    /// let b = BasicBehaviour::new_with_uuid("Behaviour 1".to_string(), Uuid::new_v4());
    /// ```
    pub fn new_with_uuid(name: String, uuid: Uuid) -> BasicBehaviour {
        BasicBehaviour { name, uuid }
    }
}

impl Behaviour for BasicBehaviour {}

impl Named for BasicBehaviour {
    /// Get the name of the [BasicBehaviour].
    fn name(&self) -> &str {
        &self.name
    }

    /// Set the name of the [BasicBehaviour].
    fn set_name(&mut self, name: String) {
        self.name = name
    }
}

impl UUIDd for BasicBehaviour {
    /// Get the [Uuid] of the [BasicBehaviour].
    fn uuid(&self) -> &Uuid {
        &self.uuid
    }

    /// Set the [Uuid] of the [BasicBehaviour].
    fn set_uuid(&mut self, u: Uuid) {
        self.uuid = u
    }
}

impl PartialEq for BasicBehaviour {
    /// Check whether two [BasicBehaviour]s are equal based solely on their
    /// [Uuid].
    fn eq(&self, other: &Self) -> bool {
        self.uuid == other.uuid
    }
}

impl Eq for BasicBehaviour {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_assigns_random_uuid() {
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());
        assert_ne!(b1.uuid(), b2.uuid());
    }

    #[test]
    fn new_assigns_name() {
        let b1 = BasicBehaviour::new("b1".to_string());
        assert_eq!(b1.name(), "b1");
    }

    #[test]
    fn new_with_uuid_assigns_uuid() {
        let uuid = Uuid::new_v4();
        let b1 = BasicBehaviour::new_with_uuid("b1".to_string(), uuid.clone());
        assert_eq!(b1.uuid(), &uuid);
    }

    #[test]
    fn new_with_uuid_assigns_name() {
        let uuid = Uuid::new_v4();
        let b1 = BasicBehaviour::new_with_uuid("b1".to_string(), uuid.clone());
        assert_eq!(b1.name(), "b1");
    }

    #[test]
    fn uuid_returns_uuid() {
        let uuid = Uuid::new_v4();
        let b = BasicBehaviour::new_with_uuid("b".to_string(), uuid.clone());
        assert_eq!(b.uuid(), &uuid);
    }

    #[test]
    fn set_uuid_sets_uuid() {
        let uuid = Uuid::new_v4();
        let mut b = BasicBehaviour::new_with_uuid("b".to_string(), uuid.clone());
        assert_eq!(b.uuid(), &uuid);
        let uuid2 = Uuid::new_v4();
        b.set_uuid(uuid2);
        assert_eq!(b.uuid(), &uuid2);
    }

    #[test]
    fn name_returns_name() {
        let b = BasicBehaviour::new("b".to_string());
        assert_eq!(b.name(), "b");
    }

    #[test]
    fn set_name_sets_name() {
        let mut b = BasicBehaviour::new("b".to_string());
        assert_eq!(b.name(), "b");
        b.set_name("bb".to_string());
        assert_eq!(b.name(), "bb");
    }

    #[test]
    fn test_equals_when_uuids_match_but_name_doesnt() {
        let uuid = Uuid::new_v4();
        let b1 = BasicBehaviour::new_with_uuid("b1".to_string(), uuid);
        let b2 = BasicBehaviour::new_with_uuid("b2".to_string(), uuid);
        assert_eq!(b1, b2)
    }

    #[test]
    fn test_equals_when_uuids_dont_match() {
        let uuid = Uuid::new_v4();
        let b1 = BasicBehaviour::new_with_uuid("b1".to_string(), uuid);
        let b2 = BasicBehaviour::new_with_uuid("b2".to_string(), Uuid::new_v4());
        assert_ne!(b1, b2)
    }
}
