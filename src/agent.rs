use std::{cell::RefCell, collections::HashMap, rc::Rc};

use anyhow::Result;
use by_address::ByAddress;
use uuid::Uuid;

use crate::{
    errors::{OutOfRangeError, UpdateActivationError},
    BehaviourPtr, BeliefPtr, SimTime, UUIDd,
};

/// A [Rc] [RefCell] pointer to an [Agent] compared by its address.
pub type AgentPtr = ByAddress<Rc<RefCell<dyn Agent>>>;

impl From<BasicAgent> for AgentPtr {
    /// Convert from a [BasicAgent] into a [AgentPtr].
    ///
    /// This consumes the [BasicAgent].
    ///
    /// # Arguments
    /// - `a`: The [BasicAgent] to convert.
    ///
    /// # Returns
    /// The [AgentPtr].
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, AgentPtr};
    ///
    /// let a = BasicAgent::new();
    /// let a_ptr = AgentPtr::from(a);
    /// ```
    ///
    /// ```
    /// use belief_spread::{BasicAgent, AgentPtr};
    ///
    /// let a = BasicAgent::new();
    /// let a_ptr: AgentPtr = a.into();
    /// ```
    fn from(a: BasicAgent) -> Self {
        ByAddress(Rc::new(RefCell::new(a)))
    }
}

/// An [Agent] which may exist in the model.
pub trait Agent: UUIDd {
    /// Gets the activation of an [Agent] towards a [BeliefPtr] at a given [SimTime].
    ///
    /// This is always between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `belief`: The [BeliefPtr].
    ///
    /// # Returns
    /// The activation, if found.
    fn get_activation(&self, time: SimTime, belief: &BeliefPtr) -> Option<f64>;

    /// Gets the activations of an [Agent] towards all [BeliefPtr]s at all [SimTime]s.
    ///
    /// This is always between -1 and +1.
    ///
    /// [BeliefPtr]s are referenced by their [Uuid]s.
    ///
    /// # Return
    /// A map from simulation time to a new map from [BeliefPtr] to the
    /// activation.
    fn get_activations(&self) -> &HashMap<SimTime, HashMap<BeliefPtr, f64>>;

    /// Sets the activation of an [Agent] towards a [BeliefPtr] at a given [SimTime].
    ///
    /// If the activation is [None], then the activation is deleted.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime] to update.
    /// - `belief`: The [BeliefPtr] to update.
    /// - `activation`: The new activation.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing went wrong, or an [Err] with an
    /// [OutOfRangeError], if the activation is not in the range [-1, +1].
    fn set_activation(
        &mut self,
        time: SimTime,
        belief: BeliefPtr,
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
    fn get_friends(&self) -> &HashMap<AgentPtr, f64>;

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
    fn get_friend_weight(&self, friend: &AgentPtr) -> Option<f64>;

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
        friend: AgentPtr,
        weight: Option<f64>,
    ) -> Result<(), OutOfRangeError>;

    /// Gets the [BehaviourPtr] the [Agent] performed at a given [SimTime].
    ///
    /// Returns the [BehaviourPtr].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    ///
    /// # Returns
    /// The [BehaviourPtr], if one was performed at `time`.
    fn get_action(&self, time: SimTime) -> Option<&BehaviourPtr>;

    /// Gets all of the [BehaviourPtr]s that the [Agent] has performed.
    ///
    /// # Returns
    /// A [HashMap] from [SimTime] to [BehaviourPtr].
    fn get_actions(&self) -> &HashMap<SimTime, BehaviourPtr>;

    /// Sets the [BehaviourPtr] the [Agent] performed at a given time.
    ///
    /// If [None], it unsets the [BehaviourPtr].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `behaviour`: The new [BehaviourPtr] that was performed at `time`.
    fn set_action(&mut self, time: SimTime, behaviour: Option<BehaviourPtr>);

    /// Gets the delta for a given [BeliefPtr].
    ///
    /// This is the value that the activation for the [BeliefPtr] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Arguments
    /// - `belief`: The [BeliefPtr].
    ///
    /// # Returns
    /// The delta for the [BeliefPtr] and this [Agent], if found.
    fn get_delta(&self, belief: &BeliefPtr) -> Option<f64>;

    /// Gets all the deltas for the [Agent].
    ///
    /// This is the value that the activation for the [BeliefPtr] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Returns
    /// A map from [BeliefPtr] to delta.
    fn get_deltas(&self) -> &HashMap<BeliefPtr, f64>;

    /// Sets the delta for a given [BeliefPtr].
    ///
    /// This is the value that the activation for the [BeliefPtr] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// If `delta` is [None], then this function removes the delta.
    ///
    /// # Arguments
    /// - `belief`: The [BeliefPtr].
    /// - `delta`: The new delta.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the delta is not strictly positive.
    fn set_delta(&mut self, belief: BeliefPtr, delta: Option<f64>) -> Result<(), OutOfRangeError>;

    /// Gets the weighted relationship between [BeliefPtr]s `b1` and `b2`.
    ///
    /// This is the compatibility for holding `b2`, given that the [Agent]
    /// already holds `b1`.
    ///
    /// This is equal to the activation of `b1`
    /// ([`Agent::get_activation`]), multiplied by the
    /// relationship between `b1` and `b2`
    /// ([`crate::Belief::get_relationship`]).
    ///
    /// Returns [None] if either activation of `b1` at time `t` is [None], or
    /// the relationship between `b1` and `b2` is [None].
    ///
    /// # Arguments
    /// - `t`: The simulation time ([SimTime]).
    /// - `b1`: The first [BeliefPtr].
    /// - `b2`: The second [BeliefPtr].
    ///
    /// # Returns
    /// The weighted relationship.
    fn weighted_relationship(&self, t: SimTime, b1: &BeliefPtr, b2: &BeliefPtr) -> Option<f64>;

    /// Gets the context for holding the [BeliefPtr] `b`.
    ///
    /// This is the compatibility for holding `b`, given all the beliefs the
    /// agent holds.
    ///
    /// This is the average of [`Agent::weighted_relationship`] for every
    /// [BeliefPtr] (as given in `beliefs).
    ///
    /// # Arguments
    /// - `time`: The simulation time ([SimTime]).
    /// - `b`: The [BeliefPtr].
    /// - `beliefs`: All the [BeliefPtr]s in existence.
    ///
    /// # Returns
    /// The context.
    fn contextualise(&self, t: SimTime, b: &BeliefPtr, beliefs: &[BeliefPtr]) -> f64;

    /// Gets the pressure the [Agent] feels to adopt a [BeliefPtr] given the
    /// actions of their friends.
    ///
    /// This does not take into account the beliefs that the [Agent] already
    /// holds.
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [BeliefPtr].
    ///
    /// # Returns
    /// The pressure
    fn pressure(&self, time: SimTime, belief: &BeliefPtr) -> f64;

    /// Gets the change in activation for the [Agent] as a result of the
    /// [BehaviourPtr]s observed.
    ///
    /// This takes into account the beliefs that the agent already holds
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [BeliefPtr].
    /// - `beliefs`: All the [BeliefPtr]s in existence.
    ///
    /// # Return
    /// - The change in activation
    fn activation_change(&self, time: SimTime, belief: &BeliefPtr, beliefs: &[BeliefPtr]) -> f64;
}

/// A [BasicAgent] is an implementation of [Agent].
pub struct BasicAgent {
    uuid: Uuid,
    activations: HashMap<SimTime, HashMap<BeliefPtr, f64>>,
    friends: HashMap<AgentPtr, f64>,
    actions: HashMap<SimTime, BehaviourPtr>,
    deltas: HashMap<BeliefPtr, f64>,
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
    /// Gets the activation of an [Agent] towards a [BeliefPtr] at a given [SimTime].
    ///
    /// This is always between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `belief`: The [BeliefPtr].
    ///
    /// # Returns
    /// The activation, if found.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, BeliefPtr};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// let b_ptr: BeliefPtr = b.into();
    /// a.set_activation(3, b_ptr.clone(), Some(0.1));
    /// assert_eq!(a.get_activation(3, &b_ptr).unwrap(), 0.1);
    /// ```
    fn get_activation(&self, time: SimTime, belief: &BeliefPtr) -> Option<f64> {
        match self.activations.get(&time) {
            Some(x) => x.get(belief).cloned(),
            None => None,
        }
    }

    /// Gets the activations of an [Agent] towards all [BeliefPtr]s at all [SimTime]s.
    ///
    /// This is always between -1 and +1.
    ///
    /// [BeliefPtr]s are referenced by their [Uuid]s.
    ///
    /// # Return
    /// A map from simulation time to a new map from [BeliefPtr] to the
    /// activation.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, BeliefPtr, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// let b_ptr: BeliefPtr = b.into();
    /// a.set_activation(3, b_ptr.clone(), Some(0.1));
    /// let activations = a.get_activations();
    /// assert_eq!(activations.len(), 1);
    /// assert_eq!(activations.get(&3).unwrap().len(), 1);
    /// assert_eq!(*activations.get(&3).unwrap().get(&b_ptr).unwrap(), 0.1);
    /// ```
    fn get_activations(&self) -> &HashMap<SimTime, HashMap<BeliefPtr, f64>> {
        &self.activations
    }

    /// Sets the activation of an [Agent] towards a [BeliefPtr] at a given [SimTime].
    ///
    /// If the activation is [None], then the activation is deleted.
    ///
    /// This is a value between -1 and +1.
    ///
    /// # Arguments
    /// - `time`: The [SimTime] to update.
    /// - `belief`: The [BeliefPtr] to update.
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
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, BeliefPtr};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// let b_ptr: BeliefPtr = b.into();
    /// a.set_activation(3, b_ptr.clone(), Some(0.1));
    /// assert_eq!(a.get_activation(3, &b_ptr).unwrap(), 0.1);
    /// a.set_activation(3, b_ptr.clone(), Some(-0.1));
    /// assert_eq!(a.get_activation(3, &b_ptr).unwrap(), -0.1);
    /// ```
    ///
    /// ## Deleting activation
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, BeliefPtr};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// let b_ptr: BeliefPtr = b.into();
    /// a.set_activation(3, b_ptr.clone(), Some(0.1));
    /// assert_eq!(a.get_activation(3, &b_ptr).unwrap(), 0.1);
    /// a.set_activation(3, b_ptr.clone(), None);
    /// assert_eq!(a.get_activation(3, &b_ptr), None);
    /// ```
    fn set_activation(
        &mut self,
        time: SimTime,
        belief: BeliefPtr,
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
    /// use belief_spread::{BasicAgent, Agent, AgentPtr, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let a2 = BasicAgent::new();
    /// let a2_ptr: AgentPtr = a2.into();
    /// a1.set_friend_weight(a2_ptr.clone(), Some(0.1)).unwrap();
    /// let friends = a1.get_friends();
    /// assert_eq!(friends.len(), 1);
    /// assert_eq!(*friends.get(&a2_ptr).unwrap(), 0.1);
    /// ```
    fn get_friends(&self) -> &HashMap<AgentPtr, f64> {
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
    /// use belief_spread::{BasicAgent, Agent, UUIDd, AgentPtr};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let a2 = BasicAgent::new();
    /// let a2_ptr: AgentPtr = a2.into();
    /// a1.set_friend_weight(a2_ptr.clone(), Some(0.1)).unwrap();
    /// assert_eq!(a1.get_friend_weight(&a2_ptr).unwrap(), 0.1)
    /// ```
    fn get_friend_weight(&self, friend: &AgentPtr) -> Option<f64> {
        self.friends.get(friend).cloned()
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
    /// use belief_spread::{BasicAgent, Agent, UUIDd, AgentPtr};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let a2 = BasicAgent::new();
    /// let a2_ptr: AgentPtr = a2.into();
    /// a1.set_friend_weight(a2_ptr.clone(), Some(0.1)).unwrap();
    /// assert_eq!(a1.get_friend_weight(&a2_ptr).unwrap(), 0.1)
    /// ```
    fn set_friend_weight(
        &mut self,
        friend: AgentPtr,
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

    /// Gets the [BehaviourPtr] the [Agent] performed at a given [SimTime].
    ///
    /// Returns the [BehaviourPtr].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    ///
    /// # Returns
    /// The [BehaviourPtr], if one was performed at `time`.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, BehaviourPtr, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let b = BasicBehaviour::new("b1".to_string());
    /// let b_ptr: BehaviourPtr = b.into();
    ///
    /// a1.set_action(2, Some(b_ptr.clone()));
    /// assert_eq!(a1.get_action(2).unwrap(), &b_ptr);
    /// ```
    fn get_action(&self, time: SimTime) -> Option<&BehaviourPtr> {
        self.actions.get(&time)
    }

    /// Gets all of the [BehaviourPtr]s that the [Agent] has performed.
    ///
    /// # Returns
    /// A [HashMap] from [SimTime] to [BehaviourPtr].
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, BehaviourPtr, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let b = BasicBehaviour::new("b1".to_string());
    /// let b_ptr: BehaviourPtr = b.into();
    ///
    /// a1.set_action(2, Some(b_ptr.clone()));
    /// let actions = a1.get_actions();
    /// assert_eq!(actions.len(), 1);
    /// assert_eq!(actions.get(&2).unwrap(), &b_ptr);
    /// ```
    fn get_actions(&self) -> &HashMap<SimTime, BehaviourPtr> {
        &self.actions
    }

    /// Sets the [BehaviourPtr] the [Agent] performed at a given time.
    ///
    /// If [None], it unsets the [BehaviourPtr].
    ///
    /// # Arguments
    /// - `time`: The [SimTime].
    /// - `behaviour`: The new [BehaviourPtr] that was performed at `time`.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, BehaviourPtr, UUIDd};
    ///
    /// let mut a1 = BasicAgent::new();
    /// let b = BasicBehaviour::new("b1".to_string());
    /// let b_ptr: BehaviourPtr = b.into();
    ///
    /// a1.set_action(2, Some(b_ptr.clone()));
    /// assert_eq!(a1.get_action(2).unwrap(), &b_ptr);
    /// ```
    fn set_action(&mut self, time: SimTime, behaviour: Option<BehaviourPtr>) {
        match behaviour {
            Some(x) => self.actions.insert(time, x),
            None => self.actions.remove(&time),
        };
    }

    /// Gets the delta for a given [BeliefPtr].
    ///
    /// This is the value that the activation for the [BeliefPtr] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Arguments
    /// - `belief`: The [BeliefPtr].
    ///
    /// # Returns
    /// The delta for the [BeliefPtr] and this [Agent], if found.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, BeliefPtr, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// let b_ptr: BeliefPtr = b.into();
    /// a.set_delta(b_ptr.clone(), Some(0.1)).unwrap();
    /// assert_eq!(a.get_delta(&b_ptr).unwrap(), 0.1);
    /// ```
    fn get_delta(&self, belief: &BeliefPtr) -> Option<f64> {
        self.deltas.get(belief).cloned()
    }

    /// Gets all the deltas for the [Agent].
    ///
    /// This is the value that the activation for the [BeliefPtr] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// # Returns
    /// A map from [BeliefPtr] to delta.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, BeliefPtr, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// let b_ptr: BeliefPtr = b.into();
    /// a.set_delta(b_ptr.clone(), Some(0.1)).unwrap();
    /// let deltas = a.get_deltas();
    /// assert_eq!(deltas.len(), 1);
    /// assert_eq!(*deltas.get(&b_ptr).unwrap(), 0.1);
    ///
    /// ```
    fn get_deltas(&self) -> &HashMap<BeliefPtr, f64> {
        &self.deltas
    }

    /// Sets the delta for a given [BeliefPtr].
    ///
    /// This is the value that the activation for the [BeliefPtr] changed by
    /// (multiplicatively) at every time step.
    ///
    /// This is a strictly positive value (i.e., > 0).
    ///
    /// If `delta` is [None], then this function removes the delta.
    ///
    /// # Arguments
    /// - `belief`: The [BeliefPtr].
    /// - `delta`: The new delta.
    ///
    /// # Returns
    /// A [Result], [Ok] if nothing is wrong, or an [Err] with a
    /// [OutOfRangeError], if the delta is not strictly positive.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBelief, BeliefPtr, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b = BasicBelief::new("b1".to_string());
    /// let b_ptr: BeliefPtr = b.into();
    /// a.set_delta(b_ptr.clone(), Some(0.1)).unwrap();
    /// assert_eq!(a.get_delta(&b_ptr).unwrap(), 0.1);
    /// ```
    fn set_delta(&mut self, belief: BeliefPtr, delta: Option<f64>) -> Result<(), OutOfRangeError> {
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

    /// Gets the weighted relationship between [BeliefPtr]s `b1` and `b2`.
    ///
    /// This is the compatibility for holding `b2`, given that the [Agent]
    /// already holds `b1`.
    ///
    /// This is equal to the activation of `b1`
    /// ([`Agent::get_activation`]), multiplied by the
    /// relationship between `b1` and `b2`
    /// ([`crate::Belief::get_relationship`]).
    ///
    /// Returns [None] if either activation of `b1` at time `t` is [None], or
    /// the relationship between `b1` and `b2` is [None].
    ///
    /// # Arguments
    /// - `t`: The simulation time ([SimTime]).
    /// - `b1`: The first [BeliefPtr].
    /// - `b2`: The second [BeliefPtr].
    ///
    /// # Returns
    /// The weighted relationship.
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{Agent, BasicAgent, BeliefPtr, BasicBelief};
    ///
    /// let mut a = BasicAgent::new();
    /// let b1 = BasicBelief::new("b1".to_string());
    /// let b1_ptr: BeliefPtr = b1.into();
    /// let b2 = BasicBelief::new("b2".to_string());
    /// let b2_ptr: BeliefPtr = b2.into();
    /// b1_ptr.borrow_mut().set_relationship(b2_ptr.clone(), Some(0.5));
    /// a.set_activation(2, b1_ptr.clone(), Some(0.5));
    ///
    /// assert_eq!(a.weighted_relationship(2, &b1_ptr, &b2_ptr).unwrap(), 0.25);
    /// ```
    fn weighted_relationship(&self, t: SimTime, b1: &BeliefPtr, b2: &BeliefPtr) -> Option<f64> {
        match self.get_activation(t, b1) {
            Some(x) => match b1.borrow().get_relationship(b2) {
                Some(y) => Some(x * y),
                None => None,
            },
            None => None,
        }
    }

    /// Gets the context for holding the [BeliefPtr] `b`.
    ///
    /// This is the compatibility for holding `b`, given all the beliefs the
    /// agent holds.
    ///
    /// This is the average of [`Agent::weighted_relationship`] for every
    /// [BeliefPtr] (as given in `beliefs).
    ///
    /// # Arguments
    /// - `time`: The simulation time ([SimTime]).
    /// - `b`: The [BeliefPtr].
    /// - `beliefs`: All the [BeliefPtr]s in existence.
    ///
    /// # Returns
    /// The context.
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{Agent, BasicAgent, BeliefPtr, BasicBelief, UUIDd};
    ///
    /// let mut a = BasicAgent::new();
    /// let b1 = BasicBelief::new("b1".to_string());
    /// let b1_ptr: BeliefPtr = b1.into();
    /// let b2 = BasicBelief::new("b2".to_string());
    /// let b2_ptr: BeliefPtr = b2.into();
    ///
    /// a.set_activation(2, b1_ptr.clone(), Some(1.0)).unwrap();
    /// a.set_activation(2, b2_ptr.clone(), Some(1.0)).unwrap();
    ///
    /// b1_ptr.borrow_mut().set_relationship(
    ///     b1_ptr.clone(),
    ///     Some(0.5),
    /// )
    /// .unwrap();
    /// b1_ptr.borrow_mut().set_relationship(b2_ptr.clone(), Some(-0.75)).unwrap();
    ///
    /// let mut beliefs: Vec<BeliefPtr> = Vec::new();
    /// beliefs.push(b1_ptr.clone());
    /// beliefs.push(b2_ptr.clone());
    ///
    /// assert_eq!(
    ///     a.contextualise(2, &b1_ptr, &beliefs),
    ///     -0.125
    /// );
    /// ```
    fn contextualise(&self, t: SimTime, b: &BeliefPtr, beliefs: &[BeliefPtr]) -> f64 {
        match beliefs.len() {
            0 => 0.0,
            size => {
                beliefs
                    .iter()
                    .map(|b2| self.weighted_relationship(t, b, b2))
                    .flatten()
                    .fold(0.0, |acc, v| acc + v)
                    / (size as f64)
            }
        }
    }

    /// Gets the pressure the [Agent] feels to adopt a [BeliefPtr] given the
    /// actions of their friends.
    ///
    /// This does not take into account the beliefs that the [Agent] already
    /// holds.
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [BeliefPtr].
    ///
    /// # Returns
    /// The pressure
    ///
    /// # Examples
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, BehaviourPtr, BasicBelief, BeliefPtr};
    /// use std::collections::HashMap;
    ///
    /// let mut agent = BasicAgent::new();
    /// let mut f1 = BasicAgent::new();
    /// let mut f2 = BasicAgent::new();
    /// let b1 = BasicBehaviour::new("b1".to_string());
    /// let b1_ptr: BehaviourPtr = b1.into();
    /// let b2 = BasicBehaviour::new("b2".to_string());
    /// let b2_ptr: BehaviourPtr = b2.into();
    ///
    /// f1.set_action(2, Some(b1_ptr.clone()));
    /// f2.set_action(2, Some(b2_ptr.clone()));
    ///
    /// let mut belief = BasicBelief::new("b1".to_string());
    /// let belief_ptr: BeliefPtr = belief.into();
    /// belief_ptr.borrow_mut().set_perception(b1_ptr.clone(), Some(0.2)).unwrap();
    /// belief_ptr.borrow_mut().set_perception(b2_ptr.clone(), Some(0.3)).unwrap();
    ///
    /// agent.set_friend_weight(f1.into(), Some(0.5));
    /// agent.set_friend_weight(f2.into(), Some(1.0));
    ///
    /// assert_eq!(agent.pressure(2, &belief_ptr), 0.2);
    /// ```
    fn pressure(&self, time: SimTime, belief: &BeliefPtr) -> f64 {
        match self.friends.len() {
            0 => 0.0,
            n => {
                self.friends
                    .iter()
                    .map(|(a, w)| {
                        a.borrow()
                            .get_action(time)
                            .map(|behaviour| {
                                belief
                                    .borrow()
                                    .get_perception(behaviour)
                                    .unwrap_or_else(|| 0.0)
                            })
                            .map(|v| v * w)
                    })
                    .flatten()
                    .sum::<f64>()
                    / (n as f64)
            }
        }
    }

    /// Gets the change in activation for the [Agent] as a result of the
    /// [BehaviourPtr]s observed.
    ///
    /// This takes into account the beliefs that the agent already holds
    ///
    /// # Arguments
    /// - `time`: The time as [SimTime].
    /// - `belief`: The [BeliefPtr].
    /// - `beliefs`: All the [BeliefPtr]s in existence.
    ///
    /// # Return
    /// - The change in activation
    ///
    /// # Examples
    ///
    /// ```
    /// use belief_spread::{BasicAgent, Agent, BasicBehaviour, BehaviourPtr, BasicBelief, BeliefPtr};
    /// use float_cmp::approx_eq;
    ///
    /// let mut agent = BasicAgent::new();
    /// let mut f1 = BasicAgent::new();
    /// let mut f2 = BasicAgent::new();
    /// let b1 = BasicBehaviour::new("b1".to_string());
    /// let b1_ptr: BehaviourPtr = b1.into();
    /// let b2 = BasicBehaviour::new("b2".to_string());
    /// let b2_ptr: BehaviourPtr = b2.into();
    ///
    /// f1.set_action(2, Some(b1_ptr.clone()));
    /// f2.set_action(2, Some(b2_ptr.clone()));
    ///
    /// let belief = BasicBelief::new("b1".to_string());
    /// let belief_ptr: BeliefPtr = belief.into();
    /// belief_ptr.borrow_mut().set_perception(b1_ptr.clone(), Some(0.2)).unwrap();
    /// belief_ptr.borrow_mut().set_perception(b2_ptr.clone(), Some(0.3)).unwrap();
    ///
    /// agent.set_friend_weight(f1.into(), Some(0.5));
    /// agent.set_friend_weight(f2.into(), Some(1.0));
    /// // Pressure is 0.2
    ///
    /// let belief2 = BasicBelief::new("b2".to_string());
    /// let belief2_ptr: BeliefPtr = belief2.into();
    /// let mut beliefs = Vec::<BeliefPtr>::new();
    /// beliefs.push(belief_ptr.clone());
    /// beliefs.push(belief2_ptr.clone());
    ///
    /// agent.set_activation(2, belief_ptr.clone(), Some(1.0)).unwrap();
    /// agent.set_activation(2, belief2_ptr.clone(), Some(1.0)).unwrap();
    /// belief_ptr.borrow_mut().set_relationship(belief_ptr.clone(), Some(0.5)).unwrap();
    /// belief_ptr.borrow_mut().set_relationship(belief2_ptr.clone(), Some(-0.75)).unwrap();
    /// // Contextualise is -0.125
    ///
    /// assert!(approx_eq!(
    ///     f64,
    ///     agent.activation_change(2, &belief_ptr, &beliefs),
    ///     0.0875,
    ///     ulps = 2
    /// ))
    fn activation_change(&self, time: SimTime, belief: &BeliefPtr, beliefs: &[BeliefPtr]) -> f64 {
        match self.pressure(time, belief) {
            p if p > 0.0 => (1.0 + self.contextualise(time, belief, beliefs)) / 2.0 * p,
            p => (1.0 - self.contextualise(time, belief, beliefs)) / 2.0 * p,
        }
    }
}

/// Updates the activation for a given [Agent] `time` and [BeliefPtr].
///
/// # Arguments
/// - `time`: The time as [SimTime].
/// - `belief`: The [BeliefPtr].
/// - `beliefs`: All the [BeliefPtr]s in existence.
///
/// # Return
/// A [Result] with nothing if [Ok], or an [Err] containing
/// [UpdateActivationError] if activation is [None] or delta is [None].
///
/// # Examples
/// ```
/// use belief_spread::{BasicAgent, Agent, BasicBehaviour, AgentPtr,
///     BehaviourPtr, BasicBelief, BeliefPtr, update_activation_for_agent};
/// use float_cmp::approx_eq;
///
/// let mut agent = BasicAgent::new();
/// let f1 = BasicAgent::new();
/// let f1_ptr: AgentPtr = f1.into();
/// let f2 = BasicAgent::new();
/// let f2_ptr: AgentPtr = f2.into();
/// let b1 = BasicBehaviour::new("b1".to_string());
/// let b1_ptr: BehaviourPtr = b1.into();
/// let b2 = BasicBehaviour::new("b2".to_string());
/// let b2_ptr: BehaviourPtr = b2.into();
///
/// f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
/// f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));
///
/// let belief = BasicBelief::new("b1".to_string());
/// let belief_ptr: BeliefPtr = belief.into();
/// belief_ptr
///     .borrow_mut()
///     .set_perception(b1_ptr.clone(), Some(0.2))
///     .unwrap();
/// belief_ptr
///     .borrow_mut()
///     .set_perception(b2_ptr.clone(), Some(0.3))
///     .unwrap();
///
/// agent.set_friend_weight(f1_ptr.clone(), Some(0.5));
/// agent.set_friend_weight(f2_ptr.clone(), Some(1.0));
///
/// // Pressure is 0.2
///
/// let belief2 = BasicBelief::new("b2".to_string());
/// let belief2_ptr: BeliefPtr = belief2.into();
/// let mut beliefs = Vec::<BeliefPtr>::new();
/// beliefs.push(belief_ptr.clone());
/// beliefs.push(belief2_ptr.clone());
///
/// agent
///     .set_activation(2, belief_ptr.clone(), Some(0.5))
///     .unwrap();
/// agent
///     .set_activation(2, belief2_ptr.clone(), Some(1.0))
///     .unwrap();
/// belief_ptr
///     .borrow_mut()
///     .set_relationship(belief_ptr.clone(), Some(1.0))
///     .unwrap();
/// belief_ptr
///     .borrow_mut()
///     .set_relationship(belief2_ptr.clone(), Some(-0.75))
///     .unwrap();
/// // Contextualise is -0.0625
///
/// // activation_change is 0.10625
/// agent.set_delta(belief_ptr.clone(), Some(1.1));
///
/// let agent_ptr: AgentPtr = agent.into();
///
/// update_activation_for_agent(&agent_ptr, 3, &belief_ptr, &beliefs).unwrap();
///
/// assert!(approx_eq!(
///     f64,
///     *agent_ptr
///         .borrow()
///         .get_activations()
///         .get(&3)
///         .unwrap()
///         .get(&belief_ptr)
///         .unwrap(),
///     0.65625,
///     ulps = 4
/// ))
/// ```
pub fn update_activation_for_agent(
    agent: &AgentPtr,
    time: SimTime,
    belief: &BeliefPtr,
    beliefs: &[BeliefPtr],
) -> Result<(), UpdateActivationError> {
    let delta = agent.borrow().get_delta(belief);
    match delta {
        None => Err(UpdateActivationError::GetDeltaNone {
            belief: belief.borrow().uuid().clone(),
        }),
        Some(d) => {
            let activation = agent.borrow().get_activation(time - 1, belief);
            match activation {
                None => Err(UpdateActivationError::GetActivationNone {
                    time: time - 1,
                    belief: belief.borrow().uuid().clone(),
                }),
                Some(a) => {
                    let activation_change =
                        { agent.borrow().activation_change(time - 1, belief, beliefs) };
                    let new_activation = (-1.0_f64).max((1.0_f64).min(d * a + activation_change));
                    agent
                        .borrow_mut()
                        .set_activation(time, belief.clone(), Some(new_activation))
                        .unwrap();
                    Ok(())
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
        let b_ptr: BeliefPtr = b.into();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let mut act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act_at_2.insert(b_ptr.clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        assert_eq!(a.get_activation(2, &b_ptr).unwrap(), 0.5);
    }

    #[test]
    fn get_activation_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        assert_eq!(a.get_activation(2, &b_ptr), None);
    }

    #[test]
    fn get_activation_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        a.activations = act;
        assert_eq!(a.get_activation(2, &b_ptr), None);
    }

    #[test]
    fn get_activations_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let mut act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act_at_2.insert(b_ptr.clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        let activations = a.get_activations();
        assert_eq!(activations.len(), 1);
        assert_eq!(activations.get(&2).unwrap().len(), 1);
        assert_eq!(*activations.get(&2).unwrap().get(&b_ptr).unwrap(), 0.5);
    }

    #[test]
    fn get_activations_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        let activations = a.get_activations();
        assert_eq!(activations.len(), 1);
        assert!(activations.get(&2).unwrap().is_empty());
    }

    #[test]
    fn get_activations_when_not_exists() {
        let mut a = BasicAgent::new();
        let act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        a.activations = act;
        let activations = a.get_activations();
        assert!(activations.is_empty());
    }

    #[test]
    fn set_activation_delete_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let mut act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act_at_2.insert(b_ptr.clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, b_ptr.clone(), None).unwrap();
        assert_eq!(a.activations.get(&2).unwrap().get(&b_ptr), None);
    }

    #[test]
    fn set_activation_delete_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, b_ptr.clone(), None).unwrap();
        assert_eq!(a.activations.get(&2).unwrap().get(&b_ptr), None);
    }

    #[test]
    fn set_activation_delete_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        a.activations = act;
        a.set_activation(2, b_ptr.clone(), None).unwrap();
        assert!(a.activations.get(&2).is_none());
    }

    #[test]
    fn set_activation_errors_when_too_low() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let expected_error = OutOfRangeError::TooLow {
            found: -1.1,
            min: -1.0,
            max: 1.0,
        };
        assert_eq!(
            a.set_activation(2, b_ptr.clone(), Some(-1.1)).unwrap_err(),
            expected_error
        );
    }

    #[test]
    fn set_activation_errors_when_too_high() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: -1.0,
            max: 1.0,
        };
        assert_eq!(
            a.set_activation(2, b_ptr.clone(), Some(1.1)).unwrap_err(),
            expected_error
        );
    }

    #[test]
    fn set_activation_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let mut act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act_at_2.insert(b_ptr.clone(), 0.5);
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, b_ptr.clone(), Some(0.2)).unwrap();
        assert_eq!(*a.activations.get(&2).unwrap().get(&b_ptr).unwrap(), 0.2);
    }

    #[test]
    fn set_activation_when_time_exists_but_belief_doesnt() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        let act_at_2: HashMap<BeliefPtr, f64> = HashMap::new();
        act.insert(2, act_at_2);
        a.activations = act;
        a.set_activation(2, b_ptr.clone(), Some(0.2)).unwrap();
        assert_eq!(*a.activations.get(&2).unwrap().get(&b_ptr).unwrap(), 0.2);
    }

    #[test]
    fn set_activation_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let act: HashMap<SimTime, HashMap<BeliefPtr, f64>> = HashMap::new();
        a.activations = act;
        a.set_activation(2, b_ptr.clone(), Some(0.2)).unwrap();
        assert_eq!(*a.activations.get(&2).unwrap().get(&b_ptr).unwrap(), 0.2);
    }

    #[test]
    fn friends_is_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.friends.is_empty())
    }

    #[test]
    fn get_friends_when_empty() {
        let mut a = BasicAgent::new();
        let friends: HashMap<AgentPtr, f64> = HashMap::new();
        a.friends = friends;
        assert!(a.get_friends().is_empty())
    }

    #[test]
    fn get_friends_when_not_empty() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();
        friends.insert(a2_ptr.clone(), 0.3);
        a.friends = friends;
        assert_eq!(a.get_friends().len(), 1);
        assert_eq!(*a.get_friends().get(&a2_ptr).unwrap(), 0.3);
    }

    #[test]
    fn get_friend_weight_when_exists() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();
        friends.insert(a2_ptr.clone(), 0.3);
        a.friends = friends;
        assert_eq!(a.get_friend_weight(&a2_ptr).unwrap(), 0.3);
    }

    #[test]
    fn get_friend_weight_when_not_exists() {
        let mut a = BasicAgent::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        let friends: HashMap<AgentPtr, f64> = HashMap::new();
        a.friends = friends;
        assert_eq!(a.get_friend_weight(&a2_ptr), None);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_valid() {
        let mut a = BasicAgent::new();
        let friends: HashMap<AgentPtr, f64> = HashMap::new();
        a.friends = friends;

        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        a.set_friend_weight(a2_ptr.clone(), Some(0.5)).unwrap();
        assert_eq!(*a.friends.get(&a2_ptr).unwrap(), 0.5);
    }

    #[test]
    fn set_friend_weight_when_exists_and_valid() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        friends.insert(a2_ptr.clone(), 0.2);
        a.friends = friends;

        a.set_friend_weight(a2_ptr.clone(), Some(0.5)).unwrap();
        assert_eq!(*a.friends.get(&a2_ptr).unwrap(), 0.5);
    }

    #[test]
    fn set_friend_weight_when_exists_and_valid_delete() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        friends.insert(a2_ptr.clone(), 0.2);
        a.friends = friends;

        a.set_friend_weight(a2_ptr.clone(), None).unwrap();
        assert_eq!(a.friends.get(&a2_ptr), None);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_valid_delete() {
        let mut a = BasicAgent::new();
        let friends: HashMap<AgentPtr, f64> = HashMap::new();
        a.friends = friends;

        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        a.set_friend_weight(a2_ptr.clone(), None).unwrap();
        assert_eq!(a.friends.get(&a2_ptr), None);
    }

    #[test]
    fn set_friend_weight_when_exists_and_too_low() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        friends.insert(a2_ptr.clone(), 0.2);
        a.friends = friends;

        let result = a.set_friend_weight(a2_ptr.clone(), Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(*a.friends.get(&a2_ptr).unwrap(), 0.2);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_too_low() {
        let mut a = BasicAgent::new();
        let friends: HashMap<AgentPtr, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        a.friends = friends;

        let result = a.set_friend_weight(a2_ptr.clone(), Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(a.friends.get(&a2_ptr), None);
    }

    #[test]
    fn set_friend_weight_when_exists_and_too_high() {
        let mut a = BasicAgent::new();
        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        friends.insert(a2_ptr.clone(), 0.2);
        a.friends = friends;

        let result = a.set_friend_weight(a2_ptr.clone(), Some(1.1));

        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(*a.friends.get(&a2_ptr).unwrap(), 0.2);
    }

    #[test]
    fn set_friend_weight_when_not_exists_and_too_high() {
        let mut a = BasicAgent::new();
        let friends: HashMap<AgentPtr, f64> = HashMap::new();
        let a2 = BasicAgent::new();
        let a2_ptr: AgentPtr = a2.into();
        a.friends = friends;

        let result = a.set_friend_weight(a2_ptr.clone(), Some(1.1));

        let expected_error = OutOfRangeError::TooHigh {
            found: 1.1,
            min: 0.0,
            max: 1.0,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(a.friends.get(&a2_ptr), None);
    }

    #[test]
    fn actions_is_initialized_empty() {
        let a = BasicAgent::new();
        assert!(a.actions.is_empty());
    }

    #[test]
    fn get_action_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        let b_ptr: BehaviourPtr = b.into();
        actions.insert(2, b_ptr.clone());
        a.actions = actions;

        assert_eq!(a.get_action(2).unwrap(), &b_ptr);
    }

    #[test]
    fn get_action_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
        a.actions = actions;

        assert_eq!(a.get_action(2), None);
    }

    #[test]
    fn get_actions_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        let b_ptr: BehaviourPtr = b.into();
        actions.insert(2, b_ptr.clone());
        a.actions = actions;

        let actions_obs = a.get_actions();

        assert_eq!(actions_obs.len(), 1);
        assert_eq!(actions_obs.get(&2).unwrap(), &b_ptr);
    }

    #[test]
    fn get_actions_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
        a.actions = actions;

        let actions_obs = a.get_actions();

        assert!(actions_obs.is_empty());
    }

    #[test]
    fn set_action_when_exists() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        let b_ptr: BehaviourPtr = b.into();
        actions.insert(2, b_ptr.clone());
        a.actions = actions;

        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        a.set_action(2, Some(b2_ptr.clone()));
        assert_eq!(a.actions.get(&2).unwrap(), &b2_ptr);
    }

    #[test]
    fn set_action_when_exists_delete() {
        let mut a = BasicAgent::new();
        let mut actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
        let b = BasicBehaviour::new("b".to_string());
        let b_ptr: BehaviourPtr = b.into();
        actions.insert(2, b_ptr.clone());
        a.actions = actions;

        a.set_action(2, None);
        assert_eq!(a.actions.get(&2), None);
    }

    #[test]
    fn set_action_when_not_exists() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
        a.actions = actions;

        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        a.set_action(2, Some(b2_ptr.clone()));
        assert_eq!(a.actions.get(&2).unwrap(), &b2_ptr);
    }

    #[test]
    fn set_action_when_not_exists_delete() {
        let mut a = BasicAgent::new();
        let actions: HashMap<SimTime, BehaviourPtr> = HashMap::new();
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
        let b_ptr: BeliefPtr = b.into();
        let mut deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        deltas.insert(b_ptr.clone(), 0.2);
        a.deltas = deltas;

        assert_eq!(a.get_delta(&b_ptr).unwrap(), 0.2);
    }

    #[test]
    fn get_delta_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        a.deltas = deltas;

        assert_eq!(a.get_delta(&b_ptr), None);
    }

    #[test]
    fn get_deltas_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        deltas.insert(b_ptr.clone(), 0.2);
        a.deltas = deltas;

        let deltas_obs = a.get_deltas();

        assert_eq!(deltas_obs.len(), 1);
        assert_eq!(*deltas_obs.get(&b_ptr).unwrap(), 0.2);
    }

    #[test]
    fn get_deltas_when_not_exists() {
        let mut a = BasicAgent::new();
        let deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        a.deltas = deltas;

        let deltas_obs = a.get_deltas();

        assert!(deltas_obs.is_empty());
    }

    #[test]
    fn set_delta_when_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        deltas.insert(b_ptr.clone(), 0.2);
        a.deltas = deltas;

        a.set_delta(b_ptr.clone(), Some(0.9)).unwrap();
        assert_eq!(*a.deltas.get(&b_ptr).unwrap(), 0.9);
    }

    #[test]
    fn set_delta_when_exists_delete() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        deltas.insert(b_ptr.clone(), 0.2);
        a.deltas = deltas;

        a.set_delta(b_ptr.clone(), None).unwrap();
        assert_eq!(a.deltas.get(&b_ptr), None);
    }

    #[test]
    fn set_delta_when_not_exists() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        a.deltas = deltas;

        a.set_delta(b_ptr.clone(), Some(0.9)).unwrap();
        assert_eq!(*a.deltas.get(&b_ptr).unwrap(), 0.9);
    }

    #[test]
    fn set_delta_when_not_exists_delete() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        a.deltas = deltas;

        a.set_delta(b_ptr.clone(), None).unwrap();
        assert_eq!(a.deltas.get(&b_ptr), None);
    }

    #[test]
    fn set_delta_when_exists_too_low() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let mut deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        deltas.insert(b_ptr.clone(), 0.2);
        a.deltas = deltas;

        let result = a.set_delta(b_ptr.clone(), Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0 + f64::EPSILON,
            max: f64::INFINITY,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(*a.deltas.get(&b_ptr).unwrap(), 0.2);
    }

    #[test]
    fn set_delta_when_not_exists_too_low() {
        let mut a = BasicAgent::new();
        let b = BasicBelief::new("b1".to_string());
        let b_ptr: BeliefPtr = b.into();
        let deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        a.deltas = deltas;

        let result = a.set_delta(b_ptr.clone(), Some(-0.1));

        let expected_error = OutOfRangeError::TooLow {
            found: -0.1,
            min: 0.0 + f64::EPSILON,
            max: f64::INFINITY,
        };

        assert_eq!(result.unwrap_err(), expected_error);

        assert_eq!(a.deltas.get(&b_ptr), None);
    }

    #[test]
    fn weighted_relationship_when_exists() {
        let mut a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b1_ptr: BeliefPtr = b1.into();
        let b2 = BasicBelief::new("b2".to_string());
        let b2_ptr: BeliefPtr = b2.into();

        a.set_activation(2, b1_ptr.clone(), Some(0.5)).unwrap();
        b1_ptr
            .borrow_mut()
            .set_relationship(b2_ptr.clone(), Some(0.1))
            .unwrap();

        assert_eq!(a.weighted_relationship(2, &b1_ptr, &b2_ptr).unwrap(), 0.05);
    }

    #[test]
    fn weighted_relationship_when_activation_not_exists() {
        let a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b1_ptr: BeliefPtr = b1.into();
        let b2 = BasicBelief::new("b2".to_string());
        let b2_ptr: BeliefPtr = b2.into();

        b1_ptr
            .borrow_mut()
            .set_relationship(b2_ptr.clone(), Some(0.1))
            .unwrap();

        assert_eq!(a.weighted_relationship(2, &b1_ptr, &b2_ptr), None);
    }

    #[test]
    fn weighted_relationship_when_relationship_not_exists() {
        let mut a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b1_ptr: BeliefPtr = b1.into();
        let b2 = BasicBelief::new("b2".to_string());
        let b2_ptr: BeliefPtr = b2.into();

        a.set_activation(2, b1_ptr.clone(), Some(0.5)).unwrap();

        assert_eq!(a.weighted_relationship(2, &b1_ptr, &b2_ptr), None);
    }

    #[test]
    fn weighted_relationship_when_not_exists() {
        let a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b1_ptr: BeliefPtr = b1.into();
        let b2 = BasicBelief::new("b2".to_string());
        let b2_ptr: BeliefPtr = b2.into();

        assert_eq!(a.weighted_relationship(2, &b1_ptr, &b2_ptr), None);
    }

    #[test]
    fn contextualise_when_beliefs_empty_returns_0() {
        let b = BasicBelief::new("b".to_string());
        let b_ptr: BeliefPtr = b.into();
        let a = BasicAgent::new();
        let beliefs: Vec<BeliefPtr> = Vec::new();

        assert_eq!(a.contextualise(2, &b_ptr, &beliefs), 0.0);
    }

    #[test]
    fn contextualise_when_beliefs_non_empty_and_all_weighted_relationships_not_none() {
        let mut a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b1_ptr: BeliefPtr = b1.into();
        let b2 = BasicBelief::new("b2".to_string());
        let b2_ptr: BeliefPtr = b2.into();

        a.set_activation(2, b1_ptr.clone(), Some(1.0)).unwrap();
        a.set_activation(2, b2_ptr.clone(), Some(1.0)).unwrap();

        b1_ptr
            .borrow_mut()
            .set_relationship(b1_ptr.clone(), Some(0.5))
            .unwrap();
        b1_ptr
            .borrow_mut()
            .set_relationship(b2_ptr.clone(), Some(-0.75))
            .unwrap();

        let mut beliefs: Vec<BeliefPtr> = Vec::new();
        beliefs.push(b1_ptr.clone());
        beliefs.push(b2_ptr.clone());

        assert_eq!(a.contextualise(2, &b1_ptr, &beliefs), -0.125);
    }

    #[test]
    fn contextualise_when_beliefs_non_empty_and_not_all_weighted_relationships_not_none() {
        let mut a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b1_ptr: BeliefPtr = b1.into();
        let b2 = BasicBelief::new("b2".to_string());
        let b2_ptr: BeliefPtr = b2.into();

        a.set_activation(2, b1_ptr.clone(), Some(0.5)).unwrap();
        a.set_activation(2, b2_ptr.clone(), Some(1.0)).unwrap();

        b1_ptr
            .borrow_mut()
            .set_relationship(b1_ptr.clone(), Some(1.0))
            .unwrap();

        let mut beliefs: Vec<BeliefPtr> = Vec::new();
        beliefs.push(b1_ptr.clone());
        beliefs.push(b2_ptr.clone());

        assert_eq!(a.contextualise(2, &b1_ptr, &beliefs), 0.25);
    }

    #[test]
    fn contextualise_when_beliefs_non_empty_and_all_weighted_relationships_none() {
        let mut a = BasicAgent::new();
        let b1 = BasicBelief::new("b1".to_string());
        let b1_ptr: BeliefPtr = b1.into();
        let b2 = BasicBelief::new("b2".to_string());
        let b2_ptr: BeliefPtr = b2.into();

        a.set_activation(2, b1_ptr.clone(), Some(0.5)).unwrap();
        a.set_activation(2, b2_ptr.clone(), Some(1.0)).unwrap();

        let mut beliefs: Vec<BeliefPtr> = Vec::new();
        beliefs.push(b1_ptr.clone());
        beliefs.push(b2_ptr.clone());

        assert_eq!(a.contextualise(2, &b1_ptr, &beliefs), 0.0);
    }

    #[test]
    fn pressure_when_no_friends() {
        let mut agent = BasicAgent::new();
        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        let friends: HashMap<AgentPtr, f64> = HashMap::new();
        agent.friends = friends;
        assert_eq!(agent.pressure(2, &belief_ptr), 0.0);
    }

    #[test]
    fn pressure_when_friends_did_nothing() {
        let agent = BasicAgent::new();
        let agent_ptr: AgentPtr = agent.into();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();

        {
            let mut mut_agent = agent_ptr.borrow_mut();
            mut_agent
                .set_friend_weight(agent_ptr.clone(), Some(0.2))
                .unwrap();
            mut_agent
                .set_friend_weight(f1_ptr.clone(), Some(0.5))
                .unwrap();
            mut_agent
                .set_friend_weight(f2_ptr.clone(), Some(1.0))
                .unwrap();
        }

        assert_eq!(agent_ptr.borrow().pressure(2, &belief_ptr), 0.0);
    }

    #[test]
    fn pressure_when_friends_did_something_but_perception_null() {
        let agent = BasicAgent::new();
        let agent_ptr: AgentPtr = agent.into();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b1_ptr: BehaviourPtr = b1.into();
        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
        f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();

        {
            let mut mut_agent = agent_ptr.borrow_mut();
            mut_agent
                .set_friend_weight(agent_ptr.clone(), Some(0.2))
                .unwrap();
            mut_agent
                .set_friend_weight(f1_ptr.clone(), Some(0.5))
                .unwrap();
            mut_agent
                .set_friend_weight(f2_ptr.clone(), Some(1.0))
                .unwrap();
        }

        assert_eq!(agent_ptr.borrow().pressure(2, &belief_ptr), 0.0);
    }

    #[test]
    fn pressure_when_friends_did_something() {
        let agent = BasicAgent::new();
        let agent_ptr: AgentPtr = agent.into();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();

        let b1 = BasicBehaviour::new("b1".to_string());
        let b1_ptr: BehaviourPtr = b1.into();
        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
        f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        belief_ptr
            .borrow_mut()
            .set_perception(b1_ptr.clone(), Some(0.2))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_perception(b2_ptr.clone(), Some(0.3))
            .unwrap();

        {
            let mut mut_agent = agent_ptr.borrow_mut();
            mut_agent
                .set_friend_weight(f1_ptr.clone(), Some(0.5))
                .unwrap();
            mut_agent
                .set_friend_weight(f2_ptr.clone(), Some(1.0))
                .unwrap();
        }

        assert_eq!(agent_ptr.borrow().pressure(2, &belief_ptr), 0.2);
    }

    #[test]
    fn activation_change_when_pressure_positive() {
        let agent = BasicAgent::new();
        let agent_ptr: AgentPtr = agent.into();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();

        let b1 = BasicBehaviour::new("b1".to_string());
        let b1_ptr: BehaviourPtr = b1.into();
        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
        f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        belief_ptr
            .borrow_mut()
            .set_perception(b1_ptr.clone(), Some(0.2))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_perception(b2_ptr.clone(), Some(0.3))
            .unwrap();

        {
            let mut mut_agent = agent_ptr.borrow_mut();
            mut_agent
                .set_friend_weight(f1_ptr.clone(), Some(0.5))
                .unwrap();
            mut_agent
                .set_friend_weight(f2_ptr.clone(), Some(1.0))
                .unwrap();
        }
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let belief2_ptr: BeliefPtr = belief2.into();
        let mut beliefs = Vec::<BeliefPtr>::new();
        beliefs.push(belief_ptr.clone());
        beliefs.push(belief2_ptr.clone());

        agent_ptr
            .borrow_mut()
            .set_activation(2, belief_ptr.clone(), Some(1.0))
            .unwrap();
        agent_ptr
            .borrow_mut()
            .set_activation(2, belief2_ptr.clone(), Some(1.0))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief_ptr.clone(), Some(0.5))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief2_ptr.clone(), Some(-0.75))
            .unwrap();
        // Contextualise is -0.125

        assert!(approx_eq!(
            f64,
            agent_ptr
                .borrow()
                .activation_change(2, &belief_ptr, &beliefs),
            0.0875,
            ulps = 2
        ))
    }

    #[test]
    fn activation_change_when_pressure_negative() {
        let agent = BasicAgent::new();
        let agent_ptr: AgentPtr = agent.into();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();

        let b1 = BasicBehaviour::new("b1".to_string());
        let b1_ptr: BehaviourPtr = b1.into();
        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
        f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        belief_ptr
            .borrow_mut()
            .set_perception(b1_ptr.clone(), Some(-0.2))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_perception(b2_ptr.clone(), Some(-0.3))
            .unwrap();

        {
            let mut mut_agent = agent_ptr.borrow_mut();
            mut_agent
                .set_friend_weight(f1_ptr.clone(), Some(0.5))
                .unwrap();
            mut_agent
                .set_friend_weight(f2_ptr.clone(), Some(1.0))
                .unwrap();
        }
        // Pressure is -0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let belief2_ptr: BeliefPtr = belief2.into();
        let mut beliefs = Vec::<BeliefPtr>::new();
        beliefs.push(belief_ptr.clone());
        beliefs.push(belief2_ptr.clone());

        agent_ptr
            .borrow_mut()
            .set_activation(2, belief_ptr.clone(), Some(1.0))
            .unwrap();
        agent_ptr
            .borrow_mut()
            .set_activation(2, belief2_ptr.clone(), Some(1.0))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief_ptr.clone(), Some(0.5))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief2_ptr.clone(), Some(-0.75))
            .unwrap();
        // Contextualise is -0.125

        assert!(approx_eq!(
            f64,
            agent_ptr
                .borrow()
                .activation_change(2, &belief_ptr, &beliefs),
            -0.1125,
            ulps = 2
        ))
    }

    #[test]
    fn update_activation_when_previous_activation_none() {
        let mut agent = BasicAgent::new();
        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        let beliefs: Vec<BeliefPtr> = Vec::new();

        let mut deltas: HashMap<BeliefPtr, f64> = HashMap::new();
        deltas.insert(belief_ptr.clone(), 1.1);

        agent.deltas = deltas;

        let agent_ptr: AgentPtr = agent.into();

        let expected_error = UpdateActivationError::GetActivationNone {
            time: 2,
            belief: belief_ptr.borrow().uuid().clone(),
        };

        assert_eq!(
            update_activation_for_agent(&agent_ptr, 3, &belief_ptr, &beliefs).unwrap_err(),
            expected_error
        );
    }

    #[test]
    fn update_activation_when_delta_none() {
        let agent = BasicAgent::new();
        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        let beliefs: Vec<BeliefPtr> = Vec::new();

        let expected_error = UpdateActivationError::GetDeltaNone {
            belief: belief_ptr.borrow().uuid().clone(),
        };

        let agent_ptr: AgentPtr = agent.into();
        assert_eq!(
            update_activation_for_agent(&agent_ptr, 2, &belief_ptr, &beliefs).unwrap_err(),
            expected_error
        );
    }

    #[test]
    fn update_activation_when_new_value_in_range() {
        let mut agent = BasicAgent::new();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b1_ptr: BehaviourPtr = b1.into();
        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
        f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        belief_ptr
            .borrow_mut()
            .set_perception(b1_ptr.clone(), Some(0.2))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_perception(b2_ptr.clone(), Some(0.3))
            .unwrap();

        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();

        friends.insert(f1_ptr.clone(), 0.5);
        friends.insert(f2_ptr.clone(), 1.0);

        agent.friends = friends;
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let belief2_ptr: BeliefPtr = belief2.into();
        let mut beliefs = Vec::<BeliefPtr>::new();
        beliefs.push(belief_ptr.clone());
        beliefs.push(belief2_ptr.clone());

        agent
            .set_activation(2, belief_ptr.clone(), Some(0.5))
            .unwrap();
        agent
            .set_activation(2, belief2_ptr.clone(), Some(1.0))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief_ptr.clone(), Some(1.0))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief2_ptr.clone(), Some(-0.75))
            .unwrap();
        // Contextualise is -0.0625

        // activation_change is 0.10625
        let mut delta: HashMap<BeliefPtr, f64> = HashMap::new();
        delta.insert(belief_ptr.clone(), 1.1);
        agent.deltas = delta;

        let agent_ptr: AgentPtr = agent.into();

        update_activation_for_agent(&agent_ptr, 3, &belief_ptr, &beliefs).unwrap();

        assert!(approx_eq!(
            f64,
            *agent_ptr
                .borrow()
                .get_activations()
                .get(&3)
                .unwrap()
                .get(&belief_ptr)
                .unwrap(),
            0.65625,
            ulps = 4
        ))
    }

    #[test]
    fn update_activation_when_new_value_too_high() {
        let mut agent = BasicAgent::new();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b1_ptr: BehaviourPtr = b1.into();
        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
        f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        belief_ptr
            .borrow_mut()
            .set_perception(b1_ptr.clone(), Some(0.2))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_perception(b2_ptr.clone(), Some(0.3))
            .unwrap();

        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();

        friends.insert(f1_ptr.clone(), 0.5);
        friends.insert(f2_ptr.clone(), 1.0);

        agent.friends = friends;
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let belief2_ptr: BeliefPtr = belief2.into();
        let mut beliefs = Vec::<BeliefPtr>::new();
        beliefs.push(belief_ptr.clone());
        beliefs.push(belief2_ptr.clone());

        agent
            .set_activation(2, belief_ptr.clone(), Some(0.5))
            .unwrap();
        agent
            .set_activation(2, belief2_ptr.clone(), Some(1.0))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief_ptr.clone(), Some(1.0))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief2_ptr.clone(), Some(-0.75))
            .unwrap();
        // Contextualise is -0.0625

        // activation_change is 0.10625
        let mut delta: HashMap<BeliefPtr, f64> = HashMap::new();
        delta.insert(belief_ptr.clone(), 100000.0);
        agent.deltas = delta;

        let agent_ptr: AgentPtr = agent.into();
        update_activation_for_agent(&agent_ptr, 3, &belief_ptr, &beliefs).unwrap();

        assert!(approx_eq!(
            f64,
            *agent_ptr
                .borrow()
                .get_activations()
                .get(&3)
                .unwrap()
                .get(&belief_ptr)
                .unwrap(),
            1.0,
            ulps = 4
        ))
    }

    #[test]
    fn update_activation_when_new_value_too_low() {
        let mut agent = BasicAgent::new();
        let f1 = BasicAgent::new();
        let f1_ptr: AgentPtr = f1.into();
        let f2 = BasicAgent::new();
        let f2_ptr: AgentPtr = f2.into();
        let b1 = BasicBehaviour::new("b1".to_string());
        let b1_ptr: BehaviourPtr = b1.into();
        let b2 = BasicBehaviour::new("b2".to_string());
        let b2_ptr: BehaviourPtr = b2.into();

        f1_ptr.borrow_mut().set_action(2, Some(b1_ptr.clone()));
        f2_ptr.borrow_mut().set_action(2, Some(b2_ptr.clone()));

        let belief = BasicBelief::new("b1".to_string());
        let belief_ptr: BeliefPtr = belief.into();
        belief_ptr
            .borrow_mut()
            .set_perception(b1_ptr.clone(), Some(0.2))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_perception(b2_ptr.clone(), Some(0.3))
            .unwrap();

        let mut friends: HashMap<AgentPtr, f64> = HashMap::new();

        friends.insert(f1_ptr.clone(), 0.5);
        friends.insert(f2_ptr.clone(), 1.0);

        agent.friends = friends;
        // Pressure is 0.2

        let belief2 = BasicBelief::new("b2".to_string());
        let belief2_ptr: BeliefPtr = belief2.into();
        let mut beliefs = Vec::<BeliefPtr>::new();
        beliefs.push(belief_ptr.clone());
        beliefs.push(belief2_ptr.clone());

        agent
            .set_activation(2, belief_ptr.clone(), Some(0.5))
            .unwrap();
        agent
            .set_activation(2, belief2_ptr.clone(), Some(1.0))
            .unwrap();

        belief_ptr
            .borrow_mut()
            .set_relationship(belief_ptr.clone(), Some(1.0))
            .unwrap();
        belief_ptr
            .borrow_mut()
            .set_relationship(belief2_ptr.clone(), Some(-0.75))
            .unwrap();
        // Contextualise is -0.0625

        // activation_change is 0.10625
        let mut delta: HashMap<BeliefPtr, f64> = HashMap::new();

        // This is a total cheat to force activation really low, officially
        // delta cannot be less than 0, but it doesn't matter.

        delta.insert(belief_ptr.clone(), -100000.0);
        agent.deltas = delta;

        let agent_ptr: AgentPtr = agent.into();
        update_activation_for_agent(&agent_ptr, 3, &belief_ptr, &beliefs).unwrap();

        assert!(approx_eq!(
            f64,
            *agent_ptr
                .borrow()
                .get_activations()
                .get(&3)
                .unwrap()
                .get(&belief_ptr)
                .unwrap(),
            -1.0,
            ulps = 4
        ))
    }

    #[test]
    fn test_from() {
        let a = BasicAgent::new();
        let uuid = a.uuid().clone();
        let a_ptr: AgentPtr = AgentPtr::from(a);
        assert_eq!(a_ptr.borrow().uuid().clone(), uuid);
    }

    #[test]
    fn test_into() {
        let a = BasicAgent::new();
        let uuid = a.uuid().clone();
        let a_ptr: AgentPtr = a.into();
        assert_eq!(a_ptr.borrow().uuid().clone(), uuid);
    }
}
