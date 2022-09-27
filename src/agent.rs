use std::collections::HashMap;

use anyhow::Result;
use uuid::Uuid;

use crate::{
    errors::{OutOfRangeError, UpdateActivationError},
    Behaviour, Belief, SimTime, UUIDd,
};

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
    /// A map from simulation time to a new map from [Belief] to the
    /// activation.
    fn get_activations(&self) -> &HashMap<SimTime, HashMap<*const dyn Belief, f64>>;

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
        belief: *const dyn Belief,
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
    /// The friends with their weight of connection.
    fn get_friends(&self) -> &HashMap<*const dyn Agent, f64>;

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
    fn get_friend_weight(&self, friend: *const dyn Agent) -> Option<f64>;

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
        friend: *const dyn Agent,
        weight: Option<f64>,
    ) -> Result<(), OutOfRangeError>;

    /// Gets the [Behaviour] the [Agent] performed at a given [SimTime].
    ///
    /// Returns the [Behaviour].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    ///
    /// # Returns
    /// The [Behaviour], if one was performed at `time`.
    fn get_action(&self, time: SimTime) -> Option<*const dyn Behaviour>;

    /// Gets all of the [Behaviour]s that the [Agent] has performed.
    ///
    /// # Returns
    /// A [HashMap] from [SimTime] to [Behaviour].
    fn get_actions(&self) -> &HashMap<SimTime, *const dyn Behaviour>;

    /// Sets the [Behaviour] the [Agent] performed at a given time.
    ///
    /// If [None], it unsets the [Behaviour].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `behaviour`: The new [Behaviour] that was performed at `time`.
    fn set_action(&mut self, time: SimTime, behaviour: Option<*const dyn Behaviour>);

    /// Gets the delta for a given [Belief].
    ///
    /// This is the value that the activation for the [Belief] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Arguments
    /// - `belief`: The [Belief].
    ///
    /// # Returns
    /// The delta for the [Belief] and this [Agent], if found.
    fn get_delta(&self, belief: &dyn Belief) -> Option<f64>;

    /// Gets all the deltas for the [Agent].
    ///
    /// This is the value that the activation for the [Belief] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Returns
    /// A map from [Belief] to delta.
    fn get_deltas(&self) -> &HashMap<*const dyn Belief, f64>;

    /// Sets the delta for a given [Belief].
    ///
    /// This is the value that the activation for the [Belief] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// If `delta` is [None], then this function removes the delta.
    ///
    /// # Arguments
    /// - `belief`: The [Belief].
    /// - `delta`: The new delta.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the delta is not strictly positive.
    fn set_delta(
        &mut self,
        belief: *const dyn Belief,
        delta: Option<f64>,
    ) -> Result<(), OutOfRangeError>;

    /// Gets the weighted relationship between [Belief]s `b1` and `b2`.
    ///
    /// This is the compatibility for holding `b2`, given that the [Agent]
    /// already holds `b1`.
    ///
    /// This is equal to the activation of `b1`
    /// ([`Agent::get_activation`]), multiplied by the
    /// relationship between `b1` and `b2`
    /// ([`Belief::get_relationship`]).
    ///
    /// Returns [None] if either activation of `b1` at time `t` is [None], or
    /// the relationship between `b1` and `b2` is [None].
    ///
    /// # Arguments
    /// - `t`: The simulation time ([SimTime]).
    /// - `b1`: The first [Belief].
    /// - `b2`: The second [Belief].
    ///
    /// # Returns
    /// The weighted relationship.
    fn weighted_relationship(
        &self,
        t: SimTime,
        b1: &dyn Belief,
        b2: *const dyn Belief,
    ) -> Option<f64>;

    /// Gets the context for holding the [Belief] `b`.
    ///
    /// This is the compatibility for holding `b`, given all the beliefs the
    /// agent holds.
    ///
    /// This is the average of [`Agent::weighted_relationship`] for every
    /// [Belief] (as given in `beliefs).
    ///
    /// # Arguments
    /// - `time`: The simulation time ([SimTime]).
    /// - `b`: The [Belief].
    /// - `beliefs`: All the [Belief]s in existence.
    ///
    /// # Returns
    /// The context.
    fn contextualise(&self, t: SimTime, b: &dyn Belief, beliefs: *const [*const dyn Belief])
        -> f64;

    /// Gets the pressure the [Agent] feels to adopt a [Belief] given the
    /// actions of their friends.
    ///
    /// This does not take into account the beliefs that the [Agent] already
    /// holds.
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [Belief].
    ///
    /// # Returns
    /// The pressure
    fn pressure(&self, time: SimTime, belief: &dyn Belief) -> f64;

    /// Gets the change in activation for the [Agent] as a result of the
    /// [Behaviour]s observed.
    ///
    /// This takes into account the beliefs that the agent already holds
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [Belief].
    /// - `beliefs`: All the [Belief]s in existence.
    ///
    /// # Return
    /// - The change in activation
    fn activation_change(
        &self,
        time: SimTime,
        belief: &dyn Belief,
        beliefs: *const [*const dyn Belief],
    ) -> f64;

    /// Updates the activation for a given `time` and [Belief].
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [Belief].
    /// - `beliefs`: All the [Belief]s in existence.
    ///
    /// # Return
    /// A [Result] with nothing if [Ok], or an [Err] containing
    /// [UpdateActivationError] if activation is [None] or delta is [None].
    unsafe fn update_activation(
        &mut self,
        time: SimTime,
        belief: *const dyn Belief,
        beliefs: *const [*const dyn Belief],
    ) -> Result<(), UpdateActivationError>;
}

/// A [BasicAgent] is an implementation of [Agent].
pub struct BasicAgent {
    uuid: Uuid,
    activations: HashMap<SimTime, HashMap<*const dyn Belief, f64>>,
    friends: HashMap<*const dyn Agent, f64>,
    actions: HashMap<SimTime, *const dyn Behaviour>,
    deltas: HashMap<*const dyn Belief, f64>,
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
            deltas: HashMap::new(),
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
            Some(x) => x.get(&(belief as *const dyn Belief)).cloned(),
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
    /// A map from simulation time to a new map from [Belief] to the
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
    /// assert_eq!(*activations.get(&3).unwrap().get(&(&b as *const dyn Belief)).unwrap(), 0.1);
    /// ```
    fn get_activations(&self) -> &HashMap<SimTime, HashMap<*const dyn Belief, f64>> {
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
        belief: *const dyn Belief,
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
                self.activations.get_mut(&time).unwrap().insert(belief, x);
                Ok(())
            }
            None => {
                match self.activations.get_mut(&time) {
                    Some(x) => x.remove(&belief),
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
    /// assert_eq!(*friends.get(&(&a2 as *const dyn Agent)).unwrap(), 0.1);
    /// ```
    fn get_friends(&self) -> &HashMap<*const dyn Agent, f64> {
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
    fn get_friend_weight(&self, friend: *const dyn Agent) -> Option<f64> {
        self.friends.get(&friend).cloned()
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
        friend: *const dyn Agent,
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
                self.friends.insert(friend, x);
                Ok(())
            }
            None => {
                self.friends.remove(&friend);
                Ok(())
            }
        }
    }

    /// Gets the [Behaviour] the [Agent] performed at a given [SimTime].
    ///
    /// Returns the [Behaviour].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    ///
    /// # Returns
    /// The [Behaviour], if one was performed at `time`.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, Behaviour, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let b = BasicBehaviour::new("b1".to_string());
    ///
    /// a1.set_action(2, Some(&b));
    /// assert_eq!(a1.get_action(2).unwrap(), &b);
    /// ```
    fn get_action(&self, time: SimTime) -> Option<*const dyn Behaviour> {
        self.actions.get(&time).cloned()
    }

    /// Gets all of the [Behaviour]s that the [Agent] has performed.
    ///
    /// # Returns
    /// A [HashMap] from [SimTime] to [Behaviour].
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
    /// assert_eq!(*actions.get(&2).unwrap(), &b);
    /// ```
    fn get_actions(&self) -> &HashMap<SimTime, *const dyn Behaviour> {
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
    /// assert_eq!(a1.get_action(2).unwrap(), &b as *const dyn Behaviour);
    /// ```
    fn set_action(&mut self, time: SimTime, behaviour: Option<*const dyn Behaviour>) {
        match behaviour {
            Some(x) => self.actions.insert(time, x),
            None => self.actions.remove(&time),
        };
    }

    /// Gets the delta for a given [Belief].
    ///
    /// This is the value that the activation for the [Belief] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Arguments
    /// - `belief`: The [Belief].
    ///
    /// # Returns
    /// The delta for the [Belief] and this [Agent], if found.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, Belief, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// a.set_delta(&b, Some(0.1)).unwrap();
    /// assert_eq!(a.get_delta(&b).unwrap(), 0.1);
    /// ```
    fn get_delta(&self, belief: &dyn Belief) -> Option<f64> {
        self.deltas.get(&(belief as *const dyn Belief)).cloned()
    }

    /// Gets all the deltas for the [Agent].
    ///
    /// This is the value that the activation for the [Belief] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Returns
    /// A map from [Belief] to delta.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, Belief, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// a.set_delta(&b, Some(0.1)).unwrap();
    /// let deltas = a.get_deltas();
    /// assert_eq!(deltas.len(), 1);
    /// assert_eq!(*deltas.get(&(&b as *const dyn Belief)).unwrap(), 0.1);
    ///
    /// ```
    fn get_deltas(&self) -> &HashMap<*const dyn Belief, f64> {
        &self.deltas
    }

    /// Sets the delta for a given [Belief].
    ///
    /// This is the value that the activation for the [Belief] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// If `delta` is [None], then this function removes the delta.
    ///
    /// # Arguments
    /// - `belief`: The [Belief].
    /// - `delta`: The new delta.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the delta is not strictly positive.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, Belief, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// a.set_delta(&b, Some(0.1)).unwrap();
    /// assert_eq!(a.get_delta(&b).unwrap(), 0.1);
    /// ```
    fn set_delta(
        &mut self,
        belief: *const dyn Belief,
        delta: Option<f64>,
    ) -> Result<(), OutOfRangeError> {
        match delta {
            None => {
                self.deltas.remove(&belief);
                Ok(())
            }
            Some(d) if d <= 0.0 => Err(OutOfRangeError::TooLow {
                found: d,
                min: 0.0 + f64::EPSILON,
                max: f64::INFINITY,
            }),
            Some(d) => {
                self.deltas.insert(belief, d);
                Ok(())
            }
        }
    }

    /// Gets the weighted relationship between [Belief]s `b1` and `b2`.
    ///
    /// This is the compatibility for holding `b2`, given that the [Agent]
    /// already holds `b1`.
    ///
    /// This is equal to the activation of `b1`
    /// ([`Agent::get_activation`]), multiplied by the
    /// relationship between `b1` and `b2`
    /// ([`Belief::get_relationship`]).
    ///
    /// Returns [None] if either activation of `b1` at time `t` is [None], or
    /// the relationship between `b1` and `b2` is [None].
    ///
    /// # Arguments
    /// - `t`: The simulation time ([SimTime]).
    /// - `b1`: The first [Belief].
    /// - `b2`: The second [Belief].
    ///
    /// # Returns
    /// The weighted relationship.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{Agent, BasicAgent, Belief, BasicBelief};
    ///
    /// let mut a = BasicAgent::new();
    /// let mut b1 = BasicBelief::new("b1".to_string());
    /// let b2 = BasicBelief::new("b2".to_string());
    /// b1.set_relationship(&b2, Some(0.5));
    /// a.set_activation(2, &b1, Some(0.5));
    ///
    /// assert_eq!(a.weighted_relationship(2, &b1, &b2).unwrap(), 0.25);
    /// ```
    fn weighted_relationship(
        &self,
        t: SimTime,
        b1: &dyn Belief,
        b2: *const dyn Belief,
    ) -> Option<f64> {
        match self.get_activation(t, b1) {
            Some(x) => match (&*b1).get_relationship(b2) {
                Some(y) => Some(x * y),
                None => None,
            },
            None => None,
        }
    }

    /// Gets the context for holding the [Belief] `b`.
    ///
    /// This is the compatibility for holding `b`, given all the beliefs the
    /// agent holds.
    ///
    /// This is the average of [`Agent::weighted_relationship`] for every
    /// [Belief] (as given in `beliefs).
    ///
    /// # Arguments
    /// - `time`: The simulation time ([SimTime]).
    /// - `b`: The [Belief].
    /// - `beliefs`: All the [Belief]s in existence. If this is null, function
    /// returns 0
    ///
    /// # Returns
    /// The context.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{Agent, BasicAgent, Belief, BasicBelief, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let mut b1 = BasicBelief::new("b1".to_string());
    /// let b2 = BasicBelief::new("b2".to_string());
    ///
    /// a.set_activation(2, &b1, Some(1.0)).unwrap();
    /// a.set_activation(2, &b2, Some(1.0)).unwrap();
    ///
    /// b1.set_relationship(
    ///     &b1,
    ///     Some(0.5),
    /// )
    /// .unwrap();
    /// b1.set_relationship(&b2, Some(-0.75)).unwrap();
    ///
    /// let mut beliefs: Vec<*const dyn Belief> = Vec::new();
    /// beliefs.push(&b1);
    /// beliefs.push(&b2);
    ///
    /// let beliefs_slice: &[*const dyn Belief] = &beliefs;
    /// assert_eq!(
    ///     a.contextualise(2, &b1, beliefs_slice),
    ///     -0.125
    /// );
    /// ```
    fn contextualise(
        &self,
        t: SimTime,
        b: &dyn Belief,
        beliefs: *const [*const dyn Belief],
    ) -> f64 {
        unsafe {
            match beliefs.as_ref() {
                None => 0.0,
                Some(bs) => match bs.len() {
                    0 => 0.0,
                    size => {
                        bs.iter()
                            .map(|&b2| self.weighted_relationship(t, b, b2))
                            .flatten()
                            .fold(0.0, |acc, v| acc + v)
                            / (size as f64)
                    }
                },
            }
        }
    }

    /// Gets the pressure the [Agent] feels to adopt a [Belief] given the
    /// actions of their friends.
    ///
    /// This does not take into account the beliefs that the [Agent] already
    /// holds.
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [Belief].
    ///
    /// # Returns
    /// The pressure
    ///
    /// # Safety
    /// Null friends are ignored.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, Behaviour, BasicBelief, Belief};
    /// use std::collections::HashMap;
    ///
    /// let mut agent = BasicAgent::new();
    /// let mut f1 = BasicAgent::new();
    /// let mut f2 = BasicAgent::new();
    /// let b1 = BasicBehaviour::new("b1".to_string());
    /// let b2 = BasicBehaviour::new("b2".to_string());
    ///
    /// f1.set_action(2, Some(&b1));
    /// f2.set_action(2, Some(&b2));
    ///
    /// let mut belief = BasicBelief::new("b1".to_string());
    /// belief.set_perception(&b1, Some(0.2)).unwrap();
    /// belief.set_perception(&b2, Some(0.3)).unwrap();
    ///
    /// agent.set_friend_weight(&f1, Some(0.5));
    /// agent.set_friend_weight(&f2, Some(1.0));
    ///
    /// assert_eq!(agent.pressure(2, &belief), 0.2);
    /// ```
    fn pressure(&self, time: SimTime, belief: &dyn Belief) -> f64 {
        match self.friends.len() {
            0 => 0.0,
            n => {
                self.friends
                    .iter()
                    .map(|(&a, w)| unsafe {
                        match a.as_ref() {
                            Some(a_ref) => a_ref
                                .get_action(time)
                                .map(|behaviour| {
                                    belief.get_perception(behaviour).unwrap_or_else(|| 0.0)
                                })
                                .map(|v| w * v),
                            None => None,
                        }
                    })
                    .flatten()
                    .sum::<f64>()
                    / (n as f64)
            }
        }
    }

    /// Gets the change in activation for the [Agent] as a result of the
    /// [Behaviour]s observed.
    ///
    /// This takes into account the beliefs that the agent already holds
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [Belief].
    /// - `beliefs`: All the [Belief]s in existence. If this is null,
    /// the function returns 0.
    ///
    /// # Return
    /// - The change in activation
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, Behaviour, BasicBelief, Belief};
    /// use float_cmp::approx_eq;
    ///
    /// let mut agent = BasicAgent::new();
    /// let mut f1 = BasicAgent::new();
    /// let mut f2 = BasicAgent::new();
    /// let b1 = BasicBehaviour::new("b1".to_string());
    /// let b2 = BasicBehaviour::new("b2".to_string());
    ///
    /// f1.set_action(2, Some(&b1));
    /// f2.set_action(2, Some(&b2));
    ///
    /// let mut belief = BasicBelief::new("b1".to_string());
    /// belief.set_perception(&b1, Some(0.2)).unwrap();
    /// belief.set_perception(&b2, Some(0.3)).unwrap();
    ///
    /// agent.set_friend_weight(&f1, Some(0.5));
    /// agent.set_friend_weight(&f2, Some(1.0));
    /// // Pressure is 0.2
    ///
    /// let belief2 = BasicBelief::new("b2".to_string());
    /// let mut beliefs = Vec::<*const dyn Belief>::new();
    /// beliefs.push(&belief);
    /// beliefs.push(&belief2);
    /// let beliefs_slice: &[*const dyn Belief] = &beliefs;
    ///
    /// agent.set_activation(2, &belief, Some(1.0)).unwrap();
    /// agent.set_activation(2, &belief2, Some(1.0)).unwrap();
    /// belief.set_relationship(&belief, Some(0.5)).unwrap();
    /// belief.set_relationship(&belief2, Some(-0.75)).unwrap();
    /// // Contextualise is -0.125
    ///
    /// assert!(approx_eq!(
    ///     f64,
    ///     agent.activation_change(2, &belief, beliefs_slice),
    ///     0.0875,
    ///     ulps = 2
    /// ))
    fn activation_change(
        &self,
        time: SimTime,
        belief: &dyn Belief,
        beliefs: *const [*const dyn Belief],
    ) -> f64 {
        match self.pressure(time, belief) {
            p if p > 0.0 => (1.0 + self.contextualise(time, belief, beliefs)) / 2.0 * p,
            p => (1.0 - self.contextualise(time, belief, beliefs)) / 2.0 * p,
        }
    }

    /// Updates the activation for a given `time` and [Belief].
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [Belief].
    /// - `beliefs`: All the [Belief]s in existence.
    ///
    /// # Safety
    /// `belief` *must* exist or this function will cause undefined behaviour /
    /// fail spectacularly.
    ///
    /// # Return
    /// A [Result] with nothing if [Ok], or an [Err] containing
    /// [UpdateActivationError] if activation is [None] or delta is [None].
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, Behaviour, BasicBelief, Belief};
    /// use float_cmp::approx_eq;
    /// let mut agent = BasicAgent::new();
    /// let mut f1 = BasicAgent::new();
    /// let mut f2 = BasicAgent::new();
    /// let b1 = BasicBehaviour::new("b1".to_string());
    /// let b2 = BasicBehaviour::new("b2".to_string());
    ///
    /// f1.set_action(2, Some(&b1));
    /// f2.set_action(2, Some(&b2));
    ///
    /// let mut belief = BasicBelief::new("b1".to_string());
    /// belief.set_perception(&b1, Some(0.2)).unwrap();
    /// belief.set_perception(&b2, Some(0.3)).unwrap();
    ///
    /// agent.set_friend_weight(&f1, Some(0.5)).unwrap();
    /// agent.set_friend_weight(&f2, Some(1.0)).unwrap();
    ///
    /// // Pressure is 0.2
    ///
    /// let belief2 = BasicBelief::new("b2".to_string());
    /// let mut beliefs = Vec::<*const dyn Belief>::new();
    /// beliefs.push(&belief);
    /// beliefs.push(&belief2);
    /// let beliefs_slice: &[*const dyn Belief] = &beliefs;
    ///
    /// agent.set_activation(2, &belief, Some(0.5)).unwrap();
    /// agent.set_activation(2, &belief2, Some(1.0)).unwrap();
    /// belief.set_relationship(&belief, Some(1.0)).unwrap();
    /// belief.set_relationship(&belief2, Some(-0.75)).unwrap();
    /// // Contextualise is -0.0625
    ///
    /// // activation_change is 0.10625
    /// agent.set_delta(&belief, Some(1.1)).unwrap();
    ///
    /// unsafe {
    ///     agent.update_activation(3, &belief, beliefs_slice).unwrap();
    /// }
    ///
    /// assert!(approx_eq!(
    ///     f64,
    ///     *agent
    ///         .get_activations()
    ///         .get(&3)
    ///         .unwrap()
    ///         .get(&(&belief as *const dyn Belief))
    ///         .unwrap(),
    ///     0.65625,
    ///     ulps = 4
    /// ))
    /// ```
    unsafe fn update_activation(
        &mut self,
        time: SimTime,
        belief: *const dyn Belief,
        beliefs: *const [*const dyn Belief],
    ) -> Result<(), UpdateActivationError> {
        match self.get_delta(&*belief) {
            None => Err(UpdateActivationError::GetDeltaNone { belief }),
            Some(d) => {
                match self.get_activation(time - 1, &*belief) {
                    None => Err(UpdateActivationError::GetActivationNone { time, belief }),
                    Some(a) => {
                        self.set_activation(
                            time,
                            belief,
                            Some((-1.0_f64).max(
                                (1.0_f64).min(
                                    d * a + self.activation_change(time - 1, &*belief, beliefs),
                                ),
                            )),
                        )
                        .unwrap();
                        Ok(())
                    }
                }
            }
        }
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
    use std::ptr::{null, slice_from_raw_parts};

    use float_cmp::approx_eq;

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
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let mut act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act_at_2.insert(&b, 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        assert_eq!(a.get_activation(2, &b).unwrap(), 0.5);
    }

    #[test]
    fn get_activation_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        assert_eq!(a.get_activation(2, &b), None);
    }

    #[test]
    fn get_activation_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        a.activations = act;
        assert_eq!(a.get_activation(2, &b), None);
    }

    #[test]
    fn get_activations_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let mut act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act_at_2.insert(&b, 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        let activations = a.get_activations();
        assert_eq!(activations.len(), 1);
        assert_eq!(activations.get(&2).unwrap().len(), 1);
        assert_eq!(
            *activations
                .get(&2)
                .unwrap()
                .get(&(&b as *const dyn Belief))
                .unwrap(),
            0.5
        );
    }

    #[test]
    fn get_activations_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        let activations = a.get_activations();
        assert_eq!(activations.len(), 1);
        assert!(activations.get(&2).unwrap().is_empty());
    }

    #[test]
    fn get_activations_when_not_exists() {
        let mut a = BasicAgent::new();
        let act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        a.activations = act;
        let activations = a.get_activations();
        assert!(activations.is_empty());
    }

    #[test]
    fn set_activation_delete_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let mut act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act_at_2.insert(&b, 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, None).unwrap();
        assert_eq!(
            a.activations
                .get(&2)
                .unwrap()
                .get(&(&b as *const dyn Belief)),
            None
        );
    }

    #[test]
    fn set_activation_delete_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, None).unwrap();
        assert_eq!(
            a.activations
                .get(&2)
                .unwrap()
                .get(&(&b as *const dyn Belief)),
            None
        );
    }

    #[test]
    fn set_activation_delete_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
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
        assert_eq!(
            a.set_activation(2, &b, Some(-1.1)).unwrap_err(),
            expected_error
        );
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
        assert_eq!(
            a.set_activation(2, &b, Some(1.1)).unwrap_err(),
            expected_error
        );
    }

    #[test]
    fn set_activation_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let mut act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act_at_2.insert(&b, 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, Some(0.2)).unwrap();
        assert_eq!(
            *a.activations
                .get(&2)
                .unwrap()
                .get(&(&b as *const dyn Belief))
                .unwrap(),
            0.2
        );
    }

    #[test]
    fn set_activation_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let mut act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        let act_at_2: HashMap<*const dyn Belief, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, &b, Some(0.2)).unwrap();
        assert_eq!(
            *a.activations
                .get(&2)
                .unwrap()
                .get(&(&b as *const dyn Belief))
                .unwrap(),
            0.2
        );
    }

    #[test]
    fn set_activation_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let act: HashMap<SimTime, HashMap<*const dyn Belief, f64>> = HashMap::new();
        a.activations = act;
        a.set_activation(2, &b, Some(0.2)).unwrap();
        assert_eq!(
            *a.activations
                .get(&2)
                .unwrap()
                .get(&(&b as *const dyn Belief))
                .unwrap(),
            0.2
        );
    }

    #[test]
    fn friends_is_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.friends.is_empty())
    }

    #[test]
    fn get_friends_when_empty() {
        let mut a = BasicAgent::new();
        let friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        a.friends = friends;
        assert!(a.get_friends().is_empty())
    }

    #[test]
    fn get_friends_when_not_empty() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        friends.insert(&a2, 0.3);
        a.friends = friends;
        assert_eq!(a.get_friends().len(), 1);
        assert_eq!(
            *a.get_friends().get(&(&a2 as *const dyn Agent)).unwrap(),
            0.3
        );
    }

    #[test]
    fn get_friend_weight_when_exists() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        friends.insert(&a2, 0.3);
        a.friends = friends;
        assert_eq!(a.get_friend_weight(&a2).unwrap(), 0.3);
    }

    #[test]
    fn get_friend_weight_when_not_exists() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        a.friends = friends;
        assert_eq!(a.get_friend_weight(&a2), None);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_valid() {
        let mut a = BasicAgent::new();
        let friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        a.friends = friends;

        let a2 = BasicAgent::new();
        a.set_friend_weight(&a2, Some(0.5)).unwrap();
        assert_eq!(*a.friends.get(&(&a2 as *const dyn Agent)).unwrap(), 0.5);
    }

    #[test]
    fn set_friend_weight_when_exists_and_valid() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(&a2, 0.2);
        a.friends = friends;

        a.set_friend_weight(&a2, Some(0.5)).unwrap();
        assert_eq!(*a.friends.get(&(&a2 as *const dyn Agent)).unwrap(), 0.5);
    }

    #[test]
    fn set_friend_weight_when_exists_and_valid_delete() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(&a2, 0.2);
        a.friends = friends;

        a.set_friend_weight(&a2, None).unwrap();
        assert_eq!(a.friends.get(&(&a2 as *const dyn Agent)), None);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_valid_delete() {
        let mut a = BasicAgent::new();
        let friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        a.friends = friends;

        let a2 = BasicAgent::new();
        a.set_friend_weight(&a2, None).unwrap();
        assert_eq!(a.friends.get(&(&a2 as *const dyn Agent)), None);
    }

    #[test]
    fn set_friend_weight_when_exists_and_too_low() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(&a2, 0.2);
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(*a.friends.get(&(&a2 as *const dyn Agent)).unwrap(), 0.2);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_too_low() {
        let mut a = BasicAgent::new();
        let friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(a.friends.get(&(&a2 as *const dyn Agent)), None);
    }

    #[test]
    fn set_friend_weight_when_exists_and_too_high() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        friends.insert(&a2, 0.2);
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(1.1));

        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(*a.friends.get(&(&a2 as *const dyn Agent)).unwrap(), 0.2);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_too_high() {
        let mut a = BasicAgent::new();
        let friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        a.friends = friends;

        let result = a.set_friend_weight(&a2, Some(1.1));

        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(a.friends.get(&(&a2 as *const dyn Agent)), None);
    }

    #[test]
    fn actions_is_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.actions.is_empty());
    }

    #[test]
    fn get_action_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, &b);
        a.actions = actions;

        assert_eq!(a.get_action(2).unwrap(), &b);
    }

    #[test]
    fn get_action_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        a.actions = actions;

        assert_eq!(a.get_action(2), None);
    }

    #[test]
    fn get_actions_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, &b);
        a.actions = actions;

        let actions_obs = a.get_actions();

        assert_eq!(actions_obs.len(), 1);
        assert_eq!(*actions_obs.get(&2).unwrap(), &b);
    }

    #[test]
    fn get_actions_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        a.actions = actions;

        let actions_obs = a.get_actions();

        assert!(actions_obs.is_empty());
    }

    #[test]
    fn set_action_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, &b);
        a.actions = actions;

        let b2 = BasicBehaviour::new("b2".to_string());

        a.set_action(2, Some(&b2));
        assert_eq!(*a.actions.get(&2).unwrap(), &b2);
    }

    #[test]
    fn set_action_when_exists_delete() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        actions.insert(2, &b);
        a.actions = actions;

        a.set_action(2, None);
        assert_eq!(a.actions.get(&2), None);
    }

    #[test]
    fn set_action_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        a.actions = actions;

        let b2 = BasicBehaviour::new("b2".to_string());

        a.set_action(2, Some(&b2));
        assert_eq!(*a.actions.get(&2).unwrap(), &b2);
    }

    #[test]
    fn set_action_when_not_exists_delete() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, *const dyn Behaviour> = HashMap::new();
        a.actions = actions;

        a.set_action(2, None);
        assert_eq!(a.actions.get(&2), None);
    }

    #[test]
    fn deltas_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.deltas.is_empty());
    }

    #[test]
    fn get_delta_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let mut deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        deltas.insert(&b, 0.2);
        a.deltas = deltas;

        assert_eq!(a.get_delta(&b).unwrap(), 0.2);
    }

    #[test]
    fn get_delta_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        a.deltas = deltas;

        assert_eq!(a.get_delta(&b), None);
    }

    #[test]
    fn get_deltas_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let mut deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        deltas.insert(&b, 0.2);
        a.deltas = deltas;

        let deltas_obs = a.get_deltas();

        assert_eq!(deltas_obs.len(), 1);
        assert_eq!(*deltas_obs.get(&(&b as *const dyn Belief)).unwrap(), 0.2);
    }

    #[test]
    fn get_deltas_when_not_exists() {
        let mut a = BasicAgent::new();
        let deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        a.deltas = deltas;

        let deltas_obs = a.get_deltas();

        assert!(deltas_obs.is_empty());
    }

    #[test]
    fn set_delta_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let mut deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        deltas.insert(&b, 0.2);
        a.deltas = deltas;

        a.set_delta(&b, Some(0.9)).unwrap();
        assert_eq!(*a.deltas.get(&(&b as *const dyn Belief)).unwrap(), 0.9);
    }

    #[test]
    fn set_delta_when_exists_delete() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let mut deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        deltas.insert(&b, 0.2);
        a.deltas = deltas;

        a.set_delta(&b, None).unwrap();
        assert_eq!(a.deltas.get(&(&b as *const dyn Belief)), None);
    }

    #[test]
    fn set_delta_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        a.deltas = deltas;

        a.set_delta(&b, Some(0.9)).unwrap();
        assert_eq!(*a.deltas.get(&(&b as *const dyn Belief)).unwrap(), 0.9);
    }

    #[test]
    fn set_delta_when_not_exists_delete() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        a.deltas = deltas;

        a.set_delta(&b, None).unwrap();
        assert_eq!(a.deltas.get(&(&b as *const dyn Belief)), None);
    }

    #[test]
    fn set_delta_when_exists_too_low() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let mut deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        deltas.insert(&b, 0.2);
        a.deltas = deltas;

        let result = a.set_delta(&b, Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0 + f64::EPSILON,
            max: f64::INFINITY,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(*a.deltas.get(&(&b as *const dyn Belief)).unwrap(), 0.2);
    }

    #[test]
    fn set_delta_when_not_exists_too_low() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        a.deltas = deltas;

        let result = a.set_delta(&b, Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0 + f64::EPSILON,
            max: f64::INFINITY,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(a.deltas.get(&(&b as *const dyn Belief)), None);
    }

    #[test]
    fn weighted_relationship_when_exists() {
        let mut a = BasicAgent::new();
        let mut b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());

        a.set_activation(2, &b1, Some(0.5)).unwrap();
        b1.set_relationship(&b2, Some(0.1)).unwrap();

        assert_eq!(a.weighted_relationship(2, &b1, &b2).unwrap(), 0.05);
    }

    #[test]
    fn weighted_relationship_when_activation_not_exists() {
        let a = BasicAgent::new();
        let mut b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());

        b1.set_relationship(&b2, Some(0.1)).unwrap();

        assert_eq!(a.weighted_relationship(2, &b1, &b2), None);
    }

    #[test]
    fn weighted_relationship_when_relationship_not_exists() {
        let mut a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());

        a.set_activation(2, &b1, Some(0.5)).unwrap();

        assert_eq!(a.weighted_relationship(2, &b1, &b2), None);
    }

    #[test]
    fn weighted_relationship_when_not_exists() {
        let a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());

        assert_eq!(a.weighted_relationship(2, &b1, &b2), None);
    }

    #[test]
    fn contextualise_when_beliefs_null_returns_0() {
        let b = BasicBelief::new("b".to_string());
        let a = BasicAgent::new();
        let beliefs_slice: *const [*const dyn Belief] = slice_from_raw_parts(null(), 0);

        assert_eq!(a.contextualise(2, &b, beliefs_slice), 0.0);
    }

    #[test]
    fn contextualise_when_beliefs_empty_returns_0() {
        let b = BasicBelief::new("b".to_string());
        let a = BasicAgent::new();
        let beliefs: Vec<*const dyn Belief> = Vec::new();
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        assert_eq!(a.contextualise(2, &b, beliefs_slice), 0.0);
    }

    #[test]
    fn contextualise_when_beliefs_non_empty_and_all_weighted_relationships_not_none() {
        let mut a = BasicAgent::new();
        let mut b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());

        a.set_activation(2, &b1, Some(1.0)).unwrap();
        a.set_activation(2, &b2, Some(1.0)).unwrap();

        b1.set_relationship(&b1, Some(0.5)).unwrap();
        b1.set_relationship(&b2, Some(-0.75)).unwrap();

        let mut beliefs: Vec<*const dyn Belief> = Vec::new();
        beliefs.push(&b1);
        beliefs.push(&b2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        assert_eq!(a.contextualise(2, &b1, beliefs_slice), -0.125);
    }

    #[test]
    fn contextualise_when_beliefs_non_empty_and_not_all_weighted_relationships_not_none() {
        let mut a = BasicAgent::new();
        let mut b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());

        a.set_activation(2, &b1, Some(0.5)).unwrap();
        a.set_activation(2, &b2, Some(1.0)).unwrap();

        b1.set_relationship(&b1, Some(1.0)).unwrap();

        let mut beliefs: Vec<*const dyn Belief> = Vec::new();
        beliefs.push(&b1);
        beliefs.push(&b2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        assert_eq!(a.contextualise(2, &b1, beliefs_slice), 0.25);
    }

    #[test]
    fn contextualise_when_beliefs_non_empty_and_all_weighted_relationships_none() {
        let mut a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b2 = BasicBelief::new("b2".to_string());

        a.set_activation(2, &b1, Some(0.5)).unwrap();
        a.set_activation(2, &b2, Some(1.0)).unwrap();

        let mut beliefs: Vec<*const dyn Belief> = Vec::new();
        beliefs.push(&b1);
        beliefs.push(&b2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        assert_eq!(a.contextualise(2, &b1, beliefs_slice), 0.0);
    }

    #[test]
    fn pressure_when_no_friends() {
        let mut agent = BasicAgent::new();
        let belief = BasicBelief::new("b1".to_string());
        let friends: HashMap<*const dyn Agent, f64> = HashMap::new();
        agent.friends = friends;
        assert_eq!(agent.pressure(2, &belief), 0.0);
    }

    #[test]
    fn pressure_when_friends_did_nothing() {
        let mut agent = BasicAgent::new();
        let f1 = BasicAgent::new();
        let f2 = BasicAgent::new();

        let belief = BasicBelief::new("b1".to_string());
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&agent, 0.2);
        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        assert_eq!(agent.pressure(2, &belief), 0.0);
    }

    #[test]
    fn pressure_when_friends_did_something_but_perception_null() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let belief = BasicBelief::new("b1".to_string());
        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&agent, 0.2);
        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        assert_eq!(agent.pressure(2, &belief), 0.0);
    }

    #[test]
    fn pressure_when_friends_did_something() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let mut belief = BasicBelief::new("b1".to_string());
        belief.set_perception(&b1, Some(0.2)).unwrap();
        belief.set_perception(&b2, Some(0.3)).unwrap();

        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        assert_eq!(agent.pressure(2, &belief), 0.2);
    }

    #[test]
    fn pressure_when_friends_did_something_but_some_null() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let mut belief = BasicBelief::new("b1".to_string());
        belief.set_perception(&b1, Some(0.2)).unwrap();
        belief.set_perception(&b2, Some(0.3)).unwrap();

        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        let f3_ref: *const BasicAgent = null();

        friends.insert(f3_ref, 0.2);

        agent.friends = friends;
        assert_eq!(agent.pressure(2, &belief), 0.4 / 3.0);
    }

    #[test]
    fn activation_change_when_pressure_positive() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let mut belief = BasicBelief::new("b1".to_string());
        belief.set_perception(&b1, Some(0.2)).unwrap();
        belief.set_perception(&b2, Some(0.3)).unwrap();

        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let mut beliefs = Vec::<*const dyn Belief>::new();
        beliefs.push(&belief);
        beliefs.push(&belief2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        agent.set_activation(2, &belief, Some(1.0)).unwrap();
        agent.set_activation(2, &belief2, Some(1.0)).unwrap();
        belief.set_relationship(&belief, Some(0.5)).unwrap();
        belief.set_relationship(&belief2, Some(-0.75)).unwrap();
        // Contextualise is -0.125

        assert!(approx_eq!(
            f64,
            agent.activation_change(2, &belief, beliefs_slice),
            0.0875,
            ulps = 2
        ))
    }

    #[test]
    fn activation_change_when_pressure_negative() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let mut belief = BasicBelief::new("b1".to_string());
        belief.set_perception(&b1, Some(-0.2)).unwrap();
        belief.set_perception(&b2, Some(-0.3)).unwrap();

        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        // Pressure is -0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let mut beliefs = Vec::<*const dyn Belief>::new();
        beliefs.push(&belief);
        beliefs.push(&belief2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        agent.set_activation(2, &belief, Some(1.0)).unwrap();
        agent.set_activation(2, &belief2, Some(1.0)).unwrap();
        belief.set_relationship(&belief, Some(0.5)).unwrap();
        belief.set_relationship(&belief2, Some(-0.75)).unwrap();
        // Contextualise is -0.125

        assert!(approx_eq!(
            f64,
            agent.activation_change(2, &belief, beliefs_slice),
            -0.1125,
            ulps = 2
        ))
    }

    #[test]
    fn update_activation_when_previous_activation_none() {
        let mut agent = BasicAgent::new();
        let belief = BasicBelief::new("b1".to_string());
        let beliefs: Vec<*const dyn Belief> = Vec::new();
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        let mut deltas: HashMap<*const dyn Belief, f64> = HashMap::new();
        deltas.insert(&belief, 1.1);

        agent.deltas = deltas;

        let expected_error = UpdateActivationError::GetActivationNone {
            time: 2,
            belief: &belief,
        };

        unsafe {
            assert_eq!(
                agent
                    .update_activation(2, &belief, beliefs_slice)
                    .unwrap_err(),
                expected_error
            );
        }
    }

    #[test]
    fn update_activation_when_delta_none() {
        let mut agent = BasicAgent::new();
        let belief = BasicBelief::new("b1".to_string());
        let beliefs: Vec<*const dyn Belief> = Vec::new();
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        let expected_error = UpdateActivationError::GetDeltaNone { belief: &belief };

        unsafe {
            assert_eq!(
                agent
                    .update_activation(2, &belief, beliefs_slice)
                    .unwrap_err(),
                expected_error
            );
        }
    }

    #[test]
    fn update_activation_when_new_value_in_range() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let mut belief = BasicBelief::new("b1".to_string());
        belief.set_perception(&b1, Some(0.2)).unwrap();
        belief.set_perception(&b2, Some(0.3)).unwrap();

        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let mut beliefs = Vec::<*const dyn Belief>::new();
        beliefs.push(&belief);
        beliefs.push(&belief2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        agent.set_activation(2, &belief, Some(0.5)).unwrap();
        agent.set_activation(2, &belief2, Some(1.0)).unwrap();
        belief.set_relationship(&belief, Some(1.0)).unwrap();
        belief.set_relationship(&belief2, Some(-0.75)).unwrap();
        // Contextualise is -0.0625

        // activation_change is 0.10625
        let mut delta: HashMap<*const dyn Belief, f64> = HashMap::new();
        delta.insert(&belief, 1.1);
        agent.deltas = delta;

        unsafe {
            agent.update_activation(3, &belief, beliefs_slice).unwrap();
        }

        assert!(approx_eq!(
            f64,
            *agent
                .activations
                .get(&3)
                .unwrap()
                .get(&(&belief as *const dyn Belief))
                .unwrap(),
            0.65625,
            ulps = 4
        ))
    }

    #[test]
    fn update_activation_when_new_value_too_high() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let mut belief = BasicBelief::new("b1".to_string());
        belief.set_perception(&b1, Some(0.2)).unwrap();
        belief.set_perception(&b2, Some(0.3)).unwrap();

        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let mut beliefs = Vec::<*const dyn Belief>::new();
        beliefs.push(&belief);
        beliefs.push(&belief2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        agent.set_activation(2, &belief, Some(0.5)).unwrap();
        agent.set_activation(2, &belief2, Some(1.0)).unwrap();
        belief.set_relationship(&belief, Some(1.0)).unwrap();
        belief.set_relationship(&belief2, Some(-0.75)).unwrap();
        // Contextualise is -0.0625

        // activation_change is 0.10625
        let mut delta: HashMap<*const dyn Belief, f64> = HashMap::new();
        delta.insert(&belief, 100000.0);
        agent.deltas = delta;

        unsafe {
            agent.update_activation(3, &belief, beliefs_slice).unwrap();
        }

        assert!(approx_eq!(
            f64,
            *agent
                .activations
                .get(&3)
                .unwrap()
                .get(&(&belief as *const dyn Belief))
                .unwrap(),
            1.0,
            ulps = 4
        ))
    }

    #[test]
    fn update_activation_when_new_value_too_low() {
        let mut agent = BasicAgent::new();
        let mut f1 = BasicAgent::new();
        let mut f2 = BasicAgent::new();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b2 = BasicBehaviour::new("b2".to_string());

        f1.set_action(2, Some(&b1));
        f2.set_action(2, Some(&b2));

        let mut belief = BasicBelief::new("b1".to_string());
        belief.set_perception(&b1, Some(0.2)).unwrap();
        belief.set_perception(&b2, Some(0.3)).unwrap();

        let mut friends: HashMap<*const dyn Agent, f64> = HashMap::new();

        friends.insert(&f1, 0.5);
        friends.insert(&f2, 1.0);

        agent.friends = friends;
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let mut beliefs = Vec::<*const dyn Belief>::new();
        beliefs.push(&belief);
        beliefs.push(&belief2);
        let beliefs_slice: &[*const dyn Belief] = &beliefs;

        agent.set_activation(2, &belief, Some(0.5)).unwrap();
        agent.set_activation(2, &belief2, Some(1.0)).unwrap();
        belief.set_relationship(&belief, Some(1.0)).unwrap();
        belief.set_relationship(&belief2, Some(-0.75)).unwrap();
        // Contextualise is -0.0625

        // activation_change is 0.10625
        let mut delta: HashMap<*const dyn Belief, f64> = HashMap::new();

        // This is a total cheat to force activation really low, officially
        // delta cannot be less than 0, but it doesn't matter.

        delta.insert(&belief, -100000.0);
        agent.deltas = delta;

        unsafe {
            agent.update_activation(3, &belief, beliefs_slice).unwrap();
        }

        assert!(approx_eq!(
            f64,
            *agent
                .activations
                .get(&3)
                .unwrap()
                .get(&(&belief as *const dyn Belief))
                .unwrap(),
            -1.0,
            ulps = 4
        ))
    }
}
