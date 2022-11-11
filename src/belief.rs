use std::{
    collections::HashMap,
    fmt::Debug,
    hash::{Hash, Hasher},
};

use crate::{errors::OutOfRangeError, Behaviour, Named, UUIDd};
use anyhow::Result;
use uuid::Uuid;

/// A Belief.
pub trait Belief: Named + UUIDd {
    /// Gets the perception, returning a [f64] if found.
    ///
    /// The perception is the amount an agent performing the behaviour can be
    /// assumed to be driven by this belief.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `behaviour`: The behaviour.
    ///
    /// # Returns
    /// The value, if found.
    fn get_perception(&self, behaviour: *const dyn Behaviour) -> Option<f64>;

    /// Sets the perception.
    ///
    /// The perception is the amount an agent performing the behaviour can be
    /// assumed to be driven by this belief.
    ///
    /// Deletes a behaviour if no perception is supplied.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `behaviour`: The [*const dyn Behaviour].
    /// - `perception`: The new perception.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the perception is not in range [-1, +1].
    fn set_perception(
        &mut self,
        behaviour: *const dyn Behaviour,
        perception: Option<f64>,
    ) -> Result<(), OutOfRangeError>;

    /// Gets the relationship, returning a [f64] if found.
    ///
    /// The relationship is the amount another belief can be deemed to be
    /// compatible with holding this belief, given that you already hold this
    /// belief.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `belief`: The other [Belief].
    ///
    /// # Returns
    /// The value, if found.
    fn get_relationship(&self, belief: *const dyn Belief) -> Option<f64>;

    /// Sets the relationship.
    ///
    /// The relationship is the amount another belief can be deemed to be
    /// compatible with holding this belief, given that you already hold this
    /// belief.
    ///
    /// Deletes a belief is no relationship is supplied.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `belief`: The other [Belief].
    /// - `relationship`: The new relationship
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the relationship is not in range [-1, +1].
    fn set_relationship(
        &mut self,
        belief: *const dyn Belief,
        relationship: Option<f64>,
    ) -> Result<(), OutOfRangeError>;
}

/// An implementation of [Belief].
#[derive(Clone)]
pub struct BasicBelief {
    name: String,
    uuid: Uuid,
    perception: HashMap<*const dyn Behaviour, f64>,
    relationship: HashMap<*const dyn Belief, f64>,
}

impl Debug for BasicBelief {
    #[cfg(not(tarpaulin_include))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BasicBelief")
            .field("name", &self.name)
            .field("uuid", &self.uuid)
            .finish()
    }
}

impl BasicBelief {
    /// Create a new [BasicBelief] with random [Uuid].
    ///
    /// # Arguments
    /// - `name`: The name of the [BasicBelief].
    ///
    /// # Returns
    /// The new [BasicBelief] with a [Uuid] generated using
    /// [`uuid::Uuid::new_v4`].
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::BasicBelief;
    ///
    /// let b = BasicBelief::new("Belief 1".to_string());
    /// ```
    pub fn new(name: String) -> Self {
        Self::new_with_uuid(name, Uuid::new_v4())
    }

    /// Create a new [BasicBelief] with specified [Uuid].
    ///
    /// # Arguments
    /// - `name`: The name of the [BasicBelief].
    /// - `uuid`: The [Uuid] of the [BasicBelief].
    ///
    /// # Returns
    /// The new [BasicBelief].
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::BasicBelief;
    /// use uuid::Uuid;
    ///
    /// let b = BasicBelief::new_with_uuid("Belief 1".to_string(), Uuid::new_v4());
    /// ```
    pub fn new_with_uuid(name: String, uuid: Uuid) -> Self {
        Self {
            name,
            uuid,
            perception: HashMap::new(),
            relationship: HashMap::new(),
        }
    }
}

impl Belief for BasicBelief {
    /// Gets the perception, returning a [f64] if found.
    ///
    /// The perception is the amount an agent performing the behaviour can be
    /// assumed to be driven by this belief.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `behaviour`: The behaviour.
    ///
    /// # Returns
    /// The value, if found.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicBelief, BasicBehaviour, Belief, *const dyn Behaviour};
    ///
    /// let mut b = BasicBelief::new("Belief 1".to_string());
    /// let behaviour = BasicBehaviour::new("Behaviour 1".to_string());
    /// let beh_ptr: *const dyn Behaviour = behaviour.into();
    /// b.set_perception(beh_ptr.clone(), Some(0.1));
    /// assert_eq!(b.get_perception(&beh_ptr).unwrap(), 0.1);
    /// ```
    fn get_perception(&self, behaviour: *const dyn Behaviour) -> Option<f64> {
        self.perception.get(&behaviour).cloned()
    }

    /// Sets the perception.
    ///
    /// The perception is the amount an agent performing the behaviour can be
    /// assumed to be driven by this belief.
    ///
    /// Deletes a behaviour if no perception is supplied.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `behaviour`: The [*const dyn Behaviour].
    /// - `perception`: The new perception.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the perception is not in range [-1, +1].
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicBelief, BasicBehaviour, Belief, *const dyn Behaviour};
    ///
    /// let mut b = BasicBelief::new("Belief 1".to_string());
    /// let behaviour = BasicBehaviour::new("Behaviour 1".to_string());
    /// let beh_ptr: *const dyn Behaviour = behaviour.into();
    /// b.set_perception(beh_ptr.clone(), Some(0.1));
    /// assert_eq!(b.get_perception(&beh_ptr).unwrap(), 0.1);
    /// ```
    fn set_perception(
        &mut self,
        behaviour: *const dyn Behaviour,
        perception: Option<f64>,
    ) -> Result<(), OutOfRangeError> {
        match perception {
            None => {
                self.perception.remove(&behaviour);
                Ok(())
            }
            Some(x) if x > 1.0 => Err(OutOfRangeError::TooHigh {
                found: x,
                min: -1.0,
                max: 1.0,
            }),
            Some(x) if x < -1.0 => Err(OutOfRangeError::TooLow {
                found: x,
                min: -1.0,
                max: 1.0,
            }),
            Some(x) => {
                self.perception.insert(behaviour, x);
                Ok(())
            }
        }
    }

    /// Gets the relationship, returning a [f64] if found.
    ///
    /// The relationship is the amount another belief can be deemed to be
    /// compatible with holding this belief, given that you already hold this
    /// belief.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `belief`: The other [Belief].
    ///
    /// # Returns
    /// The value, if found.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicBelief, BasicBehaviour, Belief, UUIDd, Named, *const dyn Belief};
    ///
    /// let mut b = BasicBelief::new("Belief 1".to_string());
    /// let b2 = BasicBelief::new("Belief 2". to_string());
    /// let b2_ptr: *const dyn Belief = b2.into();
    /// b.set_relationship(b2_ptr.clone(), Some(0.1));
    /// assert_eq!(b.get_relationship(&b2_ptr).unwrap(), 0.1);
    /// ```
    fn get_relationship(&self, belief: *const dyn Belief) -> Option<f64> {
        self.relationship.get(&belief).cloned()
    }

    /// Sets the relationship.
    ///
    /// The relationship is the amount another belief can be deemed to be
    /// compatible with holding this belief, given that you already hold this
    /// belief.
    ///
    /// Deletes a belief is no relationship is supplied.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `belief`: The other [Belief].
    /// - `relationship`: The new relationship
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the relationship is not in range [-1, +1].
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicBelief, BasicBehaviour, Belief, UUIDd, Named, *const dyn Belief};
    ///
    /// let mut b = BasicBelief::new("Belief 1".to_string());
    /// let b2 = BasicBelief::new("Belief 2". to_string());
    /// let b2_ptr: *const dyn Belief = b2.into();
    /// b.set_relationship(b2_ptr.clone(), Some(0.1));
    /// assert_eq!(b.get_relationship(&b2_ptr).unwrap(), 0.1);
    /// ```
    fn set_relationship(
        &mut self,
        belief: *const dyn Belief,
        relationship: Option<f64>,
    ) -> Result<(), OutOfRangeError> {
        match relationship {
            None => {
                self.relationship.remove(&belief);
                Ok(())
            }
            Some(x) if x > 1.0 => Err(OutOfRangeError::TooHigh {
                found: x,
                min: -1.0,
                max: 1.0,
            }),
            Some(x) if x < -1.0 => Err(OutOfRangeError::TooLow {
                found: x,
                min: -1.0,
                max: 1.0,
            }),
            Some(x) => {
                self.relationship.insert(belief, x);
                Ok(())
            }
        }
    }
}

impl Named for BasicBelief {
    /// Get the name of the [BasicBelief].
    fn name(&self) -> &str {
        &self.name
    }

    /// Set the name of the [BasicBelief].
    fn set_name(&mut self, name: String) {
        self.name = name;
    }
}

impl UUIDd for BasicBelief {
    /// Get the UUID of the [BasicBelief].
    fn uuid(&self) -> &Uuid {
        &self.uuid
    }

    /// Set the UUID of the [BasicBelief].
    fn set_uuid(&mut self, u: Uuid) {
        self.uuid = u;
    }
}

impl PartialEq for BasicBelief {
    /// Compare if two BasicBeliefs are equal, solely by their UUID.
    fn eq(&self, other: &Self) -> bool {
        self.uuid == other.uuid
    }
}

impl Hash for BasicBelief {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.uuid.hash(state);
    }
}

impl Eq for BasicBelief {}

#[cfg(test)]
mod tests {
    use crate::BasicBehaviour;
    use std::collections::hash_map::DefaultHasher;

    use super::*;

    #[test]
    fn new_with_uuid_assigns_uuid() {
        let uuid = Uuid::new_v4();
        let b = BasicBelief::new_with_uuid("b".to_string(), uuid);
        assert_eq!(b.uuid(), &uuid);
    }

    #[test]
    fn new_with_uuid_assigns_name() {
        let b = BasicBelief::new_with_uuid("b".to_string(), Uuid::new_v4());
        assert_eq!(b.name(), "b");
    }

    #[test]
    fn new_assigns_random_uuid() {
        let b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());
        assert_ne!(b1.uuid(), b2.uuid());
    }

    #[test]
    fn new_assigns_name() {
        let b = BasicBelief::new("b".to_string());
        assert_eq!(b.name(), "b");
    }

    #[test]
    fn name_returns_name() {
        let b = BasicBelief::new("b".to_string());
        assert_eq!(b.name(), "b");
    }

    #[test]
    fn set_name_sets_name() {
        let mut b = BasicBelief::new("b".to_string());
        assert_eq!(b.name(), "b");
        b.set_name("bnew".to_string());
        assert_eq!(b.name(), "bnew");
    }

    #[test]
    fn uuid_returns_uuid() {
        let uuid = Uuid::new_v4();
        let mut b = BasicBelief::new_with_uuid("b".to_string(), uuid);
        assert_eq!(b.uuid(), &uuid);
        let uuid2 = Uuid::new_v4();
        b.set_uuid(uuid2);
        assert_eq!(b.uuid(), &uuid2);
    }

    #[test]
    fn set_when_valid_and_get_relationship_when_exists() {
        let b = BasicBelief::new("belief".to_string());
        let b_ptr: *const dyn Belief = &b;
        unsafe {
            assert!((*(b_ptr as *mut dyn Belief))
                .set_relationship(b_ptr, Some(0.2))
                .is_ok());
            assert_eq!((*b_ptr).get_relationship(b_ptr).unwrap(), 0.2);
        }
    }

    #[test]
    fn get_relationship_when_not_exists() {
        let b = BasicBelief::new("belief".to_string());
        let b_ptr: *const dyn Belief = &b;
        unsafe {
            assert_eq!((*b_ptr).get_relationship(b_ptr), None);
        }
    }

    #[test]
    fn set_delete_when_valid_and_get_relationship_when_not_exists() {
        let b = BasicBelief::new("belief".to_string());
        let b_ptr: *const dyn Belief = &b;
        unsafe {
            assert!((*(b_ptr as *mut dyn Belief))
                .set_relationship(b_ptr, Some(0.2))
                .is_ok());
            assert_eq!((*b_ptr).get_relationship(b_ptr).unwrap(), 0.2);
            assert!((*(b_ptr as *mut dyn Belief))
                .set_relationship(b_ptr, None)
                .is_ok());
            assert_eq!((*b_ptr).get_relationship(b_ptr), None);
        }
    }

    #[test]
    fn set_relationship_when_too_low() {
        let b = BasicBelief::new("belief".to_string());
        let b_ptr: *const dyn Belief = &b;
        unsafe {
            let res = (*(b_ptr as *mut dyn Belief)).set_relationship(b_ptr, Some(-1.1));
            let expected_error = OutOfRangeError::TooLow {
                found: -1.1,
                min: -1.0,
                max: 1.0,
            };
            assert_eq!(res.unwrap_err(), expected_error);
        }
    }

    #[test]
    fn set_relationship_when_too_high() {
        let b = BasicBelief::new("belief".to_string());
        let b_ptr: *const dyn Belief = &b;
        unsafe {
            let res = (*(b_ptr as *mut dyn Belief)).set_relationship(b_ptr, Some(1.1));
            let expected_error = OutOfRangeError::TooHigh {
                found: 1.1,
                min: -1.0,
                max: 1.0,
            };
            assert_eq!(res.unwrap_err(), expected_error);
        }
    }

    #[test]
    fn set_when_valid_and_get_perception_when_exists() {
        let mut b = BasicBelief::new("belief".to_string());
        let beh = BasicBehaviour::new("behaviour".to_string());
        let beh_ptr: *const dyn Behaviour = &beh;
        assert!(b.set_perception(beh_ptr, Some(0.1)).is_ok());
        assert_eq!(b.get_perception(beh_ptr).unwrap(), 0.1);
    }

    #[test]
    fn get_perception_when_not_exists() {
        let b = BasicBelief::new("belief".to_string());
        let beh = BasicBehaviour::new("behaviour".to_string());
        let beh_ptr: *const dyn Behaviour = &beh;
        assert_eq!(b.get_perception(beh_ptr), None);
    }

    #[test]
    fn set_when_valid_delete_and_get_perception_when_not_exists() {
        let mut b = BasicBelief::new("belief".to_string());
        let beh = BasicBehaviour::new("behaviour".to_string());
        let beh_ptr: *const dyn Behaviour = &beh;
        assert!(b.set_perception(beh_ptr, Some(0.1)).is_ok());
        assert_eq!(b.get_perception(beh_ptr).unwrap(), 0.1);
        assert!(b.set_perception(beh_ptr, None).is_ok());
        assert_eq!(b.get_perception(beh_ptr), None);
    }

    #[test]
    fn set_perception_when_too_low() {
        let mut b = BasicBelief::new("belief".to_string());
        let beh = BasicBehaviour::new("behaviour".to_string());
        let beh_ptr: *const dyn Behaviour = &beh;
        let res = b.set_perception(beh_ptr, Some(-1.1));
        let expected_error = OutOfRangeError::TooLow {
            found: -1.1,
            min: -1.0,
            max: 1.0,
        };
        assert_eq!(res.unwrap_err(), expected_error);
    }

    #[test]
    fn set_perception_when_too_high() {
        let mut b = BasicBelief::new("belief".to_string());
        let beh = BasicBehaviour::new("behaviour".to_string());
        let beh_ptr: *const dyn Behaviour = &beh;
        let res = b.set_perception(beh_ptr, Some(1.1));
        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: -1.0,
            max: 1.0,
        };

        assert_eq!(res.unwrap_err(), expected_error);
    }

    #[test]
    fn test_equals_when_uuids_match_but_name_doesnt() {
        let uuid1 = Uuid::new_v4();
        let b1 = BasicBelief::new_with_uuid("b1".to_string(), uuid1);
        let b2 = BasicBelief::new_with_uuid("b2".to_string(), uuid1);
        assert_eq!(b1, b2);
    }

    #[test]
    fn test_equals_when_uuids_dont_match() {
        let uuid1 = Uuid::new_v4();
        let uuid2 = Uuid::new_v4();
        let b1 = BasicBelief::new_with_uuid("b1".to_string(), uuid1);
        let b2 = BasicBelief::new_with_uuid("b2".to_string(), uuid2);
        assert_ne!(b1, b2);
    }

    #[test]
    fn test_hash_when_uuids_match_but_name_doesnt() {
        let uuid1 = Uuid::new_v4();
        let b1 = BasicBelief::new_with_uuid("b1".to_string(), uuid1);
        let b2 = BasicBelief::new_with_uuid("b2".to_string(), uuid1);
        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        b1.hash(&mut hasher1);
        b2.hash(&mut hasher2);
        assert_eq!(hasher1.finish(), hasher2.finish());
    }

    #[test]
    fn test_hash_when_uuids_dont_match() {
        let uuid1 = Uuid::new_v4();
        let uuid2 = Uuid::new_v4();
        let b1 = BasicBelief::new_with_uuid("b1".to_string(), uuid1);
        let b2 = BasicBelief::new_with_uuid("b2".to_string(), uuid2);
        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        b1.hash(&mut hasher1);
        b2.hash(&mut hasher2);
        assert_ne!(hasher1.finish(), hasher2.finish());
    }
}
