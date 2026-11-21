import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
open NumberField

noncomputable section

open scoped Classical

namespace GlobalTheory.RatPointSum

variable {F : Type} [Field F] [NumberField F]

theorem norm_mixedEmbedding_le_sum (x : F) : ‖mixedEmbedding F x‖ ≤ ∑ w : InfinitePlace F, w x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => AbsoluteValue.nonneg _ _)
    (Finset.mem_univ w)

theorem norm_mixedEmbedding_nat_mul_le {κ : Type} [Fintype κ] (M : ℕ) (ξ : κ → F) :
    ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ (M : ℝ) * ∑ i, ∑ w : InfinitePlace F, w (ξ i) := by
  have h0 : ∀ i, 0 ≤ ∑ w : InfinitePlace F, w (ξ i) := fun i => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [map_mul, map_natCast, ← nsmul_eq_mul]
  refine norm_nsmul_le.trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_mixedEmbedding_le_sum (ξ i)).trans ?_) (Nat.cast_nonneg M)
  exact Finset.single_le_sum (f := fun i => ∑ w : InfinitePlace F, w (ξ i)) (fun i _ => h0 i) (Finset.mem_univ i)

end GlobalTheory.RatPointSum

