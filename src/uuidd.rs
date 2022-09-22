use uuid::Uuid;

/// Something with a [Uuid].
///
/// This trait can be used by things that should have a [Uuid].
pub trait UUIDd {
    /// Get the UUID of the object that implements this.
    fn uuid(&self) -> Uuid;

    /// Set the UUID of the object that implements this.
    ///
    /// # Arguments
    ///
    /// - `u`: The new [Uuid].
    fn set_uuid(&mut self, u: Uuid);
}
