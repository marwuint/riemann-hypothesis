import Formalism.ConjugateSelfDual.StatementRest

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

section basic

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]

def tw (e : ℤ) (χ : G F Ω →* (Qbar l)ˣ) : G F Ω →* (Qbar l)ˣ := (cyc F Ω l) ^ e * χ

end basic

end ReciprocityTheory.Gal
