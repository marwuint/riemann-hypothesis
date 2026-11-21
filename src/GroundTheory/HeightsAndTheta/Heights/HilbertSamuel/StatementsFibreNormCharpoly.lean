import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def pullField (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {x | ∃ i j, aeval y (L j) ≠ 0 ∧ x = aeval y (L i) / aeval y (L j)}

end Defs

section Inhabitants

open ProjLine

instance charZero_fnField : CharZero FnField :=
  ⟨fun a b h => by
    have h' := congrArg (fun x : FnField => (x : Kfr)) h
    simp only [SubringClass.coe_natCast] at h'
    exact_mod_cast h'⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
