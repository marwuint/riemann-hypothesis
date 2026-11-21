import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar

set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n k : ℕ} (A : HolAtlas M n)

def TypeGe (p : ℕ) (α : A.Fld) : Prop :=
  ∀ x S, (bas n).repr (α x) S ≠ 0 → p ≤ (S.filter (·.val < n)).card

end GlobalTheory.CxForm.HolAtlas
