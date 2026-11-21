import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Antisym

open MvPolynomial

section Gluing

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing segreJoin NefOnFibres mCoordIdeal)
open TensorProduct

variable {Ω : Type} [Field Ω]

def pullLat {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {ι κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (z : κ → Ω') (L : ι → AddSubgroup E) (q : ι × κ) :
    AddSubgroup (Ω' ⊗[Ω] E) :=
  AddSubgroup.closure {v | ∃ a ∈ chartRing ℤ (segreJoin (fun i => algebraMap Ω Ω' (x i)) z) q,
    ∃ e ∈ L q.1, v = a • ((1 : Ω') ⊗ₜ[Ω] e)}

instance joinFintype {K K' : Type} {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] : ∀ k, Fintype (Sum.elim ι ι' k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr k => inferInstanceAs (Fintype (ι' k))

end Gluing

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Antisym
