import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Tuple

open ReciprocityTheory.ChartRestriction.G.T0 (TVar OmS sImg)

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  {Ω : Type} [Field Ω] [Algebra K Ω]

abbrev Gens (V : Type) : Type := Σ n : ℕ, Fin (n + 1) → V

instance : Nonempty (Gens V) := ⟨⟨0, fun _ => 0⟩⟩

end Tuple

end GlobalTheory.CompanionTheory.Ar.Rec
