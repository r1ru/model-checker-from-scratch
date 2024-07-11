/// CTL formulas
pub enum CTL<P> {
    /// Atomic proposition
    AP(P),
    EX(Box<CTL<P>>),
    EG(Box<CTL<P>>),
    EU(Box<CTL<P>>, Box<CTL<P>>),
    EF(Box<CTL<P>>),
    AG(Box<CTL<P>>),
    // TODO: Support remaining formulas
}
