use std::collections::HashMap;

use anyhow::Result;
use uuid::Uuid;

use crate::{errors::OutOfRangeError, Behaviour, Belief, SimTime, UUIDd};

/// An [Agent] which may exist in the model.
pub trait Agent: UUIDd {
    /// Gets the activation of an [Agent] towards a [Belief] at a given [SimTime].
    ///
    /// This is always between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `belief`: The [Belief].
    ///
    /// # Returns
    /// The activation, if found.
    fn get_activation(&self, time: SimTime, belief: &dyn Belief) -> Option<f64>;

    /// Gets the activations of an [Agent] towards all [Belief]s at all [SimTime]s.
    ///
    /// This is always between -1 and +1.
    ///
    /// [Belief]s are referenced by their [Uuid]s.
    ///
    /// # Return
    /// A map from simulation time to a new map from [Belief] [Uuid] to the
    /// activation.
    fn get_activations(&self) -> &HashMap<SimTime, HashMap<Uuid, f64>>;

    /// Sets the activation of an [Agent] towards a [Belief] at a given [SimTime].
    ///
    /// If the activation is [None], then the activation is deleted.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime] to update.
    /// - `belief`: The [Belief] to update.
    /// - `activation`: The new activation.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing went wrong, or an [Err] with an
    /// [OutOfRangeError], if the activation is not in the range [-1, +1].
    fn set_activation(
        &mut self,
        time: SimTime,
        belief: &dyn Belief,
        activation: Option<f64>,
    ) -> Result<(), OutOfRangeError>;

    /// Gets the friends of the [Agent].
    ///
    /// This gets the friends of the [Agent] (identified by their [Uuid]) with
    /// their weight of connection.
    ///
    /// All weights are in the range [0, 1].
    ///
    /// # Returns
    /// The friends (identified by their Uuid) with their weight of connection.
    fn get_friends(&self) -> &HashMap<Uuid, f64>;

    /// Gets the weight of a friend of the [Agent].
    ///
    /// The weight will be in the range [0, 1];
    ///
    /// If they are not friends, returns [None].
    ///
    /// # Arguments
    /// - `friend`: The friend.
    ///
    /// # Returns
    /// The weight, or [None] if they are not friends.
    fn get_friend_weight(&self, friend: &dyn Agent) -> Option<f64>;

    /// Set the weight of a friend of the [Agent].
    ///
    /// If they are not friends, this adds another [Agent] as a `friend` with
    /// a supplied weight.
    ///
    /// `weight` must be in the range [0, 1].
    ///
    /// If `friend` already exists, the `weight` is overwritten.
    ///
    /// If the `weight` is [None], the `friend` is removed if they were friends.
    ///
    /// # Arguments
    /// - `friend`: The friend.
    /// - `weight`: The weight
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing went wrong, or an [Err] with an
    /// [OutOfRangeError], if the weight is not in the range [0, +1].
    fn set_friend_weight(
        &mut self,
        friend: &dyn Agent,
        weight: Option<f64>,
    ) -> Result<(), OutOfRangeError>;

    /// Gets the [Behaviour] the [Agent] performed at a given [SimTime].
    ///
    /// Returns the [Uuid] of the [Behaviour].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    ///
    /// # Returns
    /// The [Uuid] of the [Behaviour], if one was performed at `time`.
    fn get_action(&self, time: SimTime) -> Option<&Uuid>;

    /// Gets all of the [Behaviour]s that the [Agent] has performed.
    ///
    /// # Returns
    /// A [HashMap] from [SimTime] to [Behaviour] [Uuid].
    fn get_actions(&self) -> &HashMap<SimTime, Uuid>;

    /// Sets the [Behaviour] the [Agent] performed at a given time.
    ///
    /// If [None], it unsets the [Behaviour].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `behaviour`: The new [Behaviour] that was performed at `time`.
    fn set_action(&mut self, time: SimTime, behaviour: Option<&dyn Behaviour>);
}

/// A [BasicAgent] is an implementation of [Agent].
pub struct BasicAgent {
    uuid: Uuid,
    activations: HashMap<SimTime, HashMap<Uuid, f64>>,
    friends: HashMap<Uuid, f64>,
    actions: HashMap<SimTime, Uuid>,
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
        BasicAgent {
            uuid: u,
            activations: HashMap::new(),
            friends: HashMap::new(),
            actions: HashMap::new(),
        }
    }
}

impl Agent for BasicAgent {
    /// Gets the activation of an [Agent] towards a [Belief] at a given [SimTime].
    ///
    /// This is always between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `belief`: The [Belief].
    ///
    /// # Returns
    /// The activation, if found.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, Belief};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// a.set_activation(3, &b, Some(0.1));
    /// assert_eq!(a.get_activation(3, &b).unwrap(), 0.1);
    /// ```
    fn get_activation(&self, time: SimTime, belief: &dyn Belief) -> Option<f64> {
        match self.activations.get(&time) {
            Some(x) => x.get(belief.uuid()).cloned(),
            None => None,
        }
    }

    /// Gets the activations of an [Agent] towards all [Belief]s at all [SimTime]s.
    ///
    /// This is always between -1 and +1.
    ///
    /// [Belief]s are referenced by their [Uuid]s.
    ///
    /// # Return
    /// A map from simulation time to a new map from [Belief] [Uuid] to the
    /// activation.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, Belief, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// a.set_activation(3, &b, Some(0.1));
    /// let activations = a.get_activations();
    /// assert_eq!(activations.len(), 1);
    /// assert_eq!(activations.get(&3).unwrap().len(), 1);
    /// assert_eq!(*activations.get(&3).unwrap().get(b.uuid()).unwrap(), 0.1);
    /// ```
    fn get_activations(&self) -> &HashMap<SimTime, HashMap<Uuid, f64>> {
        &self.activations
    }

    /// Sets the activation of an [Agent] towards a [Belief] at a given [SimTime].
    ///
    /// If the activation is [None], then the activation is deleted.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime] to update.
    /// - `belief`: The [Belief] to update.
    /// - `activation`: The new activation.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing went wrong, or an [Err] with an
    /// [OutOfRangeError], if the activation is not in the range [-1, +1].
    ///
    /// # Examples
    ///
    /// ## Updating activation
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, Belief};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// a.set_activation(3, &b, Some(0.1));
    /// assert_eq!(a.get_activation(3, &b).unwrap(), 0.1);
    /// a.set_activation(3, &b, Some(-0.1));
    /// assert_eq!(a.get_activation(3, &b).unwrap(), -0.1);
    /// ```
    ///
    /// ## Deleting activation
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, Belief};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// a.set_activation(3, &b, Some(0.1));
    /// assert_eq!(a.get_activation(3, &b).unwrap(), 0.1);
    /// a.set_activation(3, &b, None);
    /// assert_eq!(a.get_activation(3, &b), None);
    /// ```
    fn set_activation(
        &mut self,
        time: SimTime,
        belief: &dyn Belief,
        activation: Option<f64>,
    ) -> Result<(), OutOfRangeError> {
        match activation {
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
                if !self.activations.contains_key(&time) {
                    self.activations.insert(time, HashMap::new());
                }
                self.activations
                    .get_mut(&time)
                    .unwrap()
                    .insert(*belief.uuid(), x);
                Ok(())
            }
            None => {
                match self.activations.get_mut(&time) {
                    Some(x) => x.remove(belief.uuid()),
                    None => None,
                };
                Ok(())
            }
        }
    }

    /// Gets the friends of the [Agent].
    ///
    /// This gets the friends of the [Agent] (identified by their [Uuid]) with
    /// their weight of connection.
    ///
    /// All weights are in the range [0, 1].
    ///
    /// # Returns
    /// The friends (identified by their Uuid) with their weight of connection.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let a2 = BasicAgent::new();
    /// a1.set_friend_weight(&a2, Some(0.1)).unwrap();
    /// let friends = a1.get_friends();
    /// assert_eq!(friends.len(), 1);
    /// assert_eq!(*friends.get(a2.uuid()).unwrap(), 0.1);
    /// ```
    fn get_friends(&self) -> &HashMap<Uuid, f64> {
        &self.friends
    }

    /// Gets the weight of a friend of the [Agent].
    ///
    /// The weight will be in the range [0, 1];
    ///
    /// If they are not friends, returns [None].
    ///
    /// # Arguments
    /// - `friend`: The friend.
    ///
    /// # Returns
    /// The weight, or [None] if they are not friends.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let a2 = BasicAgent::new();
    /// a1.set_friend_weight(&a2, Some(0.1)).unwrap();
    /// assert_eq!(a1.get_friend_weight(&a2).unwrap(), 0.1)
    /// ```
    fn get_friend_weight(&self, friend: &dyn Agent) -> Option<f64> {
        self.friends.get(friend.uuid()).cloned()
    }

    /// Set the weight of a friend of the [Agent].
    ///
    /// If they are not friends, this adds another [Agent] as a `friend` with
    /// a supplied weight.
    ///
    /// `weight` must be in the range [0, 1].
    ///
    /// If `friend` already exists, the `weight` is overwritten.
    ///
    /// If the `weight` is [None], the `friend` is removed if they were friends.
    ///
    /// # Arguments
    /// - `friend`: The friend.
    /// - `weight`: The weight
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing went wrong, or an [Err] with an
    /// [OutOfRangeError], if the weight is not in the range [0, +1].
    ///
    /// # Warning
    ///
    /// If `friend` is the same [Agent], you'll get into errors with two references.
    ///
    /// A nasty hack is to do somsething like so:
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let a1_cl = BasicAgent::new_with_uuid(a1.uuid().clone());
    /// a1.set_friend_weight(&a1_cl, Some(0.1)).unwrap();
    /// assert_eq!(a1.get_friend_weight(&a1).unwrap(), 0.1)
    /// ```
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let a2 = BasicAgent::new();
    /// a1.set_friend_weight(&a2, Some(0.1)).unwrap();
    /// assert_eq!(a1.get_friend_weight(&a2).unwrap(), 0.1)
    /// ```
    fn set_friend_weight(
        &mut self,
        friend: &dyn Agent,
        weight: Option<f64>,
    ) -> Result<(), OutOfRangeError> {
        match weight {
            Some(x) if x > 1.0 => Err(OutOfRangeError::TooHigh {
                found: x,
                min: 0.0,
                max: 1.0,
            }),
            Some(x) if x < 0.0 => Err(OutOfRangeError::TooLow {
                found: x,
                min: 0.0,
                max: 1.0,
            }),
            Some(x) => {
                self.friends.insert(friend.uuid().clone(), x);
                Ok(())
            }
            None => {
                self.friends.remove(friend.uuid());
                Ok(())
            }
        }
    }

    /// Gets the [Behaviour] the [Agent] performed at a given [SimTime].
    ///
    /// Returns the [Uuid] of the [Behaviour].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    ///
    /// # Returns
    /// The [Uuid] of the [Behaviour], if one was performed at `time`.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, Behaviour, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let b = BasicBehaviour::new("b1".to_string());
    ///
    /// a1.set_action(2, Some(&b));
    /// assert_eq!(a1.get_action(2).unwrap(), b.uuid());
    /// ```
    fn get_action(&self, time: SimTime) -> Option<&Uuid> {
        self.actions.get(&time)
    }

    /// Gets all of the [Behaviour]s that the [Agent] has performed.
    ///
    /// # Returns
    /// A [HashMap] from [SimTime] to [Behaviour] [Uuid].
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, Behaviour, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let b = BasicBehaviour::new("b1".to_string());
    ///
    /// a1.set_action(2, Some(&b));
    /// let actions = a1.get_actions();
    /// assert_eq!(actions.len(), 1);
    /// assert_eq!(actions.get(&2).unwrap(), b.uuid());
    /// ```
    fn get_actions(&self) -> &HashMap<SimTime, Uuid> {
        &self.actions
    }

    /// Sets the [Behaviour] the [Agent] performed at a given time.
    ///
    /// If [None], it unsets the [Behaviour].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `behaviour`: The new [Behaviour] that was performed at `time`.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, Behaviour, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let b = BasicBehaviour::new("b1".to_string());
    ///
    /// a1.set_action(2, Some(&b));
    /// assert_eq!(a1.get_action(2).unwrap(), b.uuid());
    /// ```
    fn set_action(&mut self, time: SimTime, behaviour: Option<&dyn Behaviour>) {
        match behaviour {
            Some(x) => self.actions.insert(time, x.uuid().clone()),
            None => self.actions.remove(&time),
        };
    }
}

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
    use crate::{BasicBehaviour, BasicBelief};

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

    #[test]
    fn activation_is_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.activations.is_empty());
    }

    #[test]
    fn get_activation_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let mut act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act_at_2.insert(b.uuid().clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        assert_eq!(a.get_activation(2, &b).unwrap(), 0.5);
    }

    #[test]
    fn get_activation_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        assert_eq!(a.get_activation(2, &b), None);
    }

    #[test]
    fn get_activation_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        a.activations = act;
        assert_eq!(a.get_activation(2, &b), None);
    }

    #[test]
    fn get_activations_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let mut act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act_at_2.insert(b.uuid().clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        let activations = a.get_activations();
        assert_eq!(activations.len(), 1);
        assert_eq!(activations.get(&2).unwrap().len(), 1);
        assert_eq!(*activations.get(&2).unwrap().get(b.uuid()).unwrap(), 0.5);
    }

    #[test]
    fn get_activations_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        let activations = a.get_activations();
        assert_eq!(activations.len(), 1);
        assert!(activations.get(&2).unwrap().is_empty());
    }

    #[test]
    fn get_activations_when_not_exists() {
        let mut a = BasicAgent::new();
        let act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        a.activations = act;
        let activations = a.get_activations();
        assert!(activations.is_empty());
    }

    #[test]
    fn set_activation_delete_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let mut act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act_at_2.insert(b.uuid().clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, None).unwrap();
        assert_eq!(a.activations.get(&2).unwrap().get(b.uuid()), None);
    }

    #[test]
    fn set_activation_delete_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, None).unwrap();
        assert_eq!(a.activations.get(&2).unwrap().get(b.uuid()), None);
    }

    #[test]
    fn set_activation_delete_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        a.activations = act;
        a.set_activation(2, &b, None).unwrap();
        assert_eq!(a.activations.get(&2), None);
    }

    #[test]
    fn set_activation_errors_when_too_low() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let expected_error = OutOfRangeError::TooLow {
            found: -1.1,
            min: -1.0,
            max: 1.0,
        };
        match a.set_activation(2, &b, Some(-1.1)) {
            Ok(()) => assert!(false, "This should have errored!"),
            Err(x) if x == expected_error => assert!(true),
            Err(_) => assert!(false, "Wrong error"),
        }
    }

    #[test]
    fn set_activation_errors_when_too_high() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: -1.0,
            max: 1.0,
        };
        match a.set_activation(2, &b, Some(1.1)) {
            Ok(()) => assert!(false, "This should have errored!"),
            Err(x) if x == expected_error => assert!(true),
            Err(_) => assert!(false, "Wrong error"),
        }
    }

    #[test]
    fn set_activation_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let mut act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act_at_2.insert(b.uuid().clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, Some(0.2)).unwrap();
        assert_eq!(*a.activations.get(&2).unwrap().get(b.uuid()).unwrap(), 0.2);
    }

    #[test]
    fn set_activation_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        let act_at_2: HashMap<Uuid, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, Some(0.2)).unwrap();
        assert_eq!(*a.activations.get(&2).unwrap().get(b.uuid()).unwrap(), 0.2);
    }

    #[test]
    fn set_activation_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let act: HashMap<SimTime, HashMap<Uuid, f64>> = HashMap::new();
        a.activations = act;
        a.set_activation(2, &b, Some(0.2)).unwrap();
        assert_eq!(*a.activations.get(&2).unwrap().get(b.uuid()).unwrap(), 0.2);
    }

    #[test]
    fn friends_is_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.friends.is_empty())
    }

    #[test]
    fn get_friends_when_empty() {
        let mut a = BasicAgent::new();
        let friends: HashMap<Uuid, f64> = HashMap::new();
        a.friends = friends;
        assert!(a.get_friends().is_empty())
    }

    #[test]
    fn get_friends_when_not_empty() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let mut friends: HashMap<Uuid, f64> = HashMap::new();
        friends.insert(a2.uuid, 0.3);
        a.friends = friends;
        assert_eq!(a.get_friends().len(), 1);
        assert_eq!(*a.get_friends().get(a2.uuid()).unwrap(), 0.3);
    }

    #[test]
    fn get_friend_weight_when_exists() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let mut friends: HashMap<Uuid, f64> = HashMap::new();
        friends.insert(a2.uuid, 0.3);
        a.friends = friends;
        assert_eq!(a.get_friend_weight(&a2).unwrap(), 0.3);
    }

    #[test]
    fn get_friend_weight_when_not_exists() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let friends: HashMap<Uuid, f64> = HashMap::new();
        a.friends = friends;
        assert_eq!(a.get_friend_weight(&a2), None);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_valid() {
        let mut a = BasicAgent::new();
        let friends: HashMap<Uuid, f64> = HashMap::new();
        a.friends = friends;

        let a2 = BasicAgent::new();
        a.set_friend_weight(&a2, Some(0.5)).unwrap();
        assert_eq!(*a.friends.get(a2.uuid()).unwrap(), 0.5);
    }

    #[test]
    fn set_friend_weight_when_exists_and_valid() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<Uuid, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(a2.uuid.clone(), 0.2);
        a.friends = friends;

        a.set_friend_weight(&a2, Some(0.5)).unwrap();
        assert_eq!(*a.friends.get(a2.uuid()).unwrap(), 0.5);
    }

    #[test]
    fn set_friend_weight_when_exists_and_valid_delete() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<Uuid, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(a2.uuid.clone(), 0.2);
        a.friends = friends;

        a.set_friend_weight(&a2, None).unwrap();
        assert_eq!(a.friends.get(a2.uuid()), None);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_valid_delete() {
        let mut a = BasicAgent::new();
        let friends: HashMap<Uuid, f64> = HashMap::new();
        a.friends = friends;

        let a2 = BasicAgent::new();
        a.set_friend_weight(&a2, None).unwrap();
        assert_eq!(a.friends.get(a2.uuid()), None);
    }

    #[test]
    fn set_friend_weight_when_exists_and_too_low() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<Uuid, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(a2.uuid.clone(), 0.2);
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0,
            max: 1.0,
        };

        match result {
            Ok(()) => assert!(false, "This should have errored"),
            Err(x) if x == expected_error => assert!(true),
            Err(_) => assert!(false, "This gave the wrong error"),
        };

        assert_eq!(*a.friends.get(a2.uuid()).unwrap(), 0.2);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_too_low() {
        let mut a = BasicAgent::new();
        let friends: HashMap<Uuid, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0,
            max: 1.0,
        };

        match result {
            Ok(()) => assert!(false, "This should have errored"),
            Err(x) if x == expected_error => assert!(true),
            Err(_) => assert!(false, "This gave the wrong error"),
        };

        assert_eq!(a.friends.get(a2.uuid()), None);
    }

    #[test]
    fn set_friend_weight_when_exists_and_too_high() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<Uuid, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(a2.uuid.clone(), 0.2);
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(1.1));

        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: 0.0,
            max: 1.0,
        };

        match result {
            Ok(()) => assert!(false, "This should have errored"),
            Err(x) if x == expected_error => assert!(true),
            Err(_) => assert!(false, "This gave the wrong error"),
        };

        assert_eq!(*a.friends.get(a2.uuid()).unwrap(), 0.2);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_too_high() {
        let mut a = BasicAgent::new();
        let friends: HashMap<Uuid, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(1.1));

        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: 0.0,
            max: 1.0,
        };

        match result {
            Ok(()) => assert!(false, "This should have errored"),
            Err(x) if x == expected_error => assert!(true),
            Err(_) => assert!(false, "This gave the wrong error"),
        };

        assert_eq!(a.friends.get(a2.uuid()), None);
    }

    #[test]
    fn actions_is_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.actions.is_empty());
    }

    #[test]
    fn get_action_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, Uuid> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, b.uuid().clone());
        a.actions = actions;

        assert_eq!(a.get_action(2).unwrap(), b.uuid());
    }

    #[test]
    fn get_action_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, Uuid> = HashMap::new();
        a.actions = actions;

        assert_eq!(a.get_action(2), None);
    }

    #[test]
    fn get_actions_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, Uuid> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, b.uuid().clone());
        a.actions = actions;

        let actions_obs = a.get_actions();

        assert_eq!(actions_obs.len(), 1);
        assert_eq!(actions_obs.get(&2).unwrap(), b.uuid());
    }

    #[test]
    fn get_actions_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, Uuid> = HashMap::new();
        a.actions = actions;

        let actions_obs = a.get_actions();

        assert!(actions_obs.is_empty());
    }

    #[test]
    fn set_action_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, Uuid> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, b.uuid().clone());
        a.actions = actions;

        let b2 = BasicBehaviour::new("b2".to_string());

        a.set_action(2, Some(&b2));
        assert_eq!(a.actions.get(&2).unwrap(), b2.uuid());
    }

    #[test]
    fn set_action_when_exists_delete() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, Uuid> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, b.uuid().clone());
        a.actions = actions;

        a.set_action(2, None);
        assert_eq!(a.actions.get(&2), None);
    }

    #[test]
    fn set_action_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, Uuid> = HashMap::new();
        a.actions = actions;

        let b2 = BasicBehaviour::new("b2".to_string());

        a.set_action(2, Some(&b2));
        assert_eq!(a.actions.get(&2).unwrap(), b2.uuid());
    }

    #[test]
    fn set_action_when_not_exists_delete() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, Uuid> = HashMap::new();
        a.actions = actions;

        a.set_action(2, None);
        assert_eq!(a.actions.get(&2), None);
    }
}
