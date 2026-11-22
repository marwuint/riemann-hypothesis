import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_trans {m : ℕ} {x y z : Qbar l} (h : Cg m x y) (h' : Cg m y z) : Cg m x z := by
  unfold Cg at *
  have hm := IsUltrametricDist.norm_add_le_max (x - y) (y - z)
  rw [sub_add_sub_cancel] at hm
  exact hm.trans (max_le h h')

theorem cg_symm {m : ℕ} {x y : Qbar l} (h : Cg m x y) : Cg m y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_sum {m : ℕ} {ι : Type} (S : Finset ι) {x y : ι → Qbar l} (h : ∀ i ∈ S, Cg m (x i) (y i)) :
    Cg m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

theorem cg_mul_left {m : ℕ} {o x y : Qbar l} (ho : ‖o‖ ≤ 1) (h : Cg m x y) : Cg m (o * x) (o * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖o‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ho (norm_nonneg _)
    _ = ‖x - y‖ := one_mul _
    _ ≤ _ := h

end GlobalTheory.KumUnit
