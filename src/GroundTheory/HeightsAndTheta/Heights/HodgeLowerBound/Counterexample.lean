import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo Line

section Curve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem inter_constLine_eq [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (M : ℝ) (hM : 0 < M) :
    I W 1 ![constLine M hM] = Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  have hfin : Finite (projPts W) := by
    rw [degC_eq_card_projPts] at hdeg
    exact (Nat.card_pos_iff.mp hdeg).2
  have key : ∀ φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral W φ (fun _ ↦ (1 : ℝ)) = degC W := by
    intro φ
    obtain rfl : φ = Fin.elim0 := funext fun j ↦ j.elim0
    rw [PtsIntegralPoints.homogProof K ι W (fun _ ↦ 1) hH hfin (fun _ _ _ _ ↦ rfl),
      degC_eq_card_projPts]
    have := Fintype.ofFinite (projPts W)
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  unfold arInt
  rw [h, Inter.Conservation.ptsIntegral_const, key]
  ring

end Curve

section Point

def ptIdeal : Ideal (MRing (PBlk 2)) := orbitIdeal samplePoint

end Point

end GroundTheory.Heights₂.Heights.LowerBoundFree
