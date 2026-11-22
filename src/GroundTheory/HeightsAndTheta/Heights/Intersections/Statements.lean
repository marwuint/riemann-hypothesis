import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def DegreeGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
      ptsIntegral P (pot L) (fun _ => 1) =
        NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) (fun j => (L j).a)

theorem isSmoothHerm_fsLine (n : ℕ) : IsSmoothHerm (fsLine n) := by
  have hfun : (fsLine n).h = fun z => ∏ k : Unit, Real.sqrt (∑ i : Fin n, ‖z ⟨k, i⟩‖ ^ 2) := by
    funext z
    simp only [fsLine, HermLine.ofMetrics, fsMetric, Pi.one_apply, zpow_one,
      EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ContDiffOn.sqrt ?_ fun z hz => ?_
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, PBlk n k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

end

end GroundTheory.Heights₂.Heights.Inter
