import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open DirichletCharacter

section PrimePower

variable {l v : ℕ} [hl : Fact l.Prime]

private instance bounds_neZero : NeZero (l ^ v) := ⟨pow_ne_zero _ hl.out.ne_zero⟩

end PrimePower

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

end KStar.Ram
