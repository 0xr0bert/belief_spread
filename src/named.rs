/// Something with a name.
///
/// This trait represents something that is named.
pub trait Named {
    /// Get the name of the object with this trait.
    fn name(&self) -> &str;
}
