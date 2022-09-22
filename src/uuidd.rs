use uuid::Uuid;

/// Something with a [Uuid].
///
/// This trait can be used by things that should have a [Uuid].
pub trait UUIDd {
    /// Get the UUID of the struct that implements this.
    fn uuid(&self) -> Uuid;
}
