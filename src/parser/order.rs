#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Order {
    /// Any other order of token
    Lowest,
    /// Prefix of '<' and '>'
    /// This operator will surround expression
    TakeByte,
    /// '<<' and '>>'
    Shift,
    /// '+' and '-'
    AddAndSub,
    /// '*' and '/'
    MulAndDiv,
}
