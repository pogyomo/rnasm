#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Order {
    /// Any other order of token
    Lowest,
    /// '+' and '-'
    AddAndSub,
    /// '*' and '/'
    MulAndDiv,
}
