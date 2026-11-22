import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowStable

theorem X_mul_pderiv_totalDegree_le {σ : Type} (u v : σ) (g : MvPolynomial σ ℂ) :
    (X u * pderiv v g).totalDegree ≤ g.totalDegree := by
  classical
  have key : ∀ m ∈ (pderiv v g).support, (m.sum fun _ e => e) + 1 ≤ g.totalDegree := by
    intro m hm
    have hc : coeff (m + Finsupp.single v 1) g ≠ 0 := by
      rw [mem_support_iff, coeff_pderiv] at hm
      intro h
      rw [h, zero_mul] at hm
      exact hm rfl
    have h1 := le_totalDegree (mem_support_iff.2 hc)
    have h2 : ((m + Finsupp.single v 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [h2] at h1
    exact h1
  by_cases h0 : pderiv v g = 0
  · rw [h0, mul_zero, totalDegree_zero]; exact Nat.zero_le _
  · obtain ⟨m, hm⟩ := (support_nonempty).2 h0
    have hm1 := key m hm
    have hle : (pderiv v g).totalDegree ≤ g.totalDegree - 1 :=
      Finset.sup_le fun m' hm' => by have := key m' hm'; show (m'.sum fun _ e => e) ≤ _; omega
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega

end GlobalTheory.LowStable
