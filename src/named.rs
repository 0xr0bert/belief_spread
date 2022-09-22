/// Something with a name.
///
/// This trait represents something that is named.
pub trait Named {
    /// Get the name of the object with this trait.
    fn name(&self) -> &str;

    /// Set the name of the object with this trait.
    ///
    /// # Arguments
    /// - `name`: The new name as a [String].
    fn set_name(&mut self, name: String);
}
