import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.GradedNorm

open Matrix

theorem det_mem {C : Type} [Field C] (W : ValuationSubring C) {k : ℕ} (A : Matrix (Fin k) (Fin k) C)
    (h : ∀ i j, A i j ∈ W) : A.det ∈ W := by
  rw [Matrix.det_apply']
  exact W.toSubring.sum_mem fun σ _ =>
    W.toSubring.mul_mem (intCast_mem W.toSubring _) (W.toSubring.prod_mem fun i _ => h _ _)

theorem mem_of_mulVec {C : Type} [Field C] (W : ValuationSubring C) {m n : ℕ} (ι : Fin n → Fin m)
    (u : Matrix (Fin m) (Fin n) C) (huW : ∀ i j, u i j ∈ W)
    (hu0 : ∀ i j : Fin n, i < j → u (ι i) j = 0) (hu1 : ∀ i, u (ι i) i = 1) (y : Fin n → C)
    (hy : ∀ s, (u *ᵥ y) s ∈ W) (i : Fin n) : y i ∈ W := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have h1 : y i = (u *ᵥ y) (ι i) - ∑ j ∈ Finset.univ.erase i, u (ι i) j * y j := by
      rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hu1]
      ring
    rw [h1]
    refine W.toSubring.sub_mem (hy _) (W.toSubring.sum_mem fun j hj => ?_)
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · exact W.toSubring.mul_mem (huW _ _) (ih j h)
    · rw [hu0 _ _ h, zero_mul]
      exact W.toSubring.zero_mem

end GlobalTheory.FlagEmb.GradedNorm
