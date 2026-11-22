import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HcParamSubIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BigCellMemUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpenCellNorm

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

theorem bigCell_mem_of_weight {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec) {q : (Fin r → ℂ) × ℂ}
    (hq : bcWeight k r (Tz k r z) (Tz k r z') q ≠ 0) : bigCell k r q.1 (μsec q.2) ∈ UH (Hpk k r) := by
  unfold bcWeight at hq
  split_ifs at hq with h
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hq
    refine GlobalTheory.bigCell_mem_unitary k r _ _ (fun a ha => ?_) (hs.2 _ (lt_of_le_of_ne h fun e => ?_)).1
    · refine Finset.prod_ne_zero_iff.1 h1 a (Finset.mem_univ a) ?_
      rw [ha, norm_zero]
      exact zero_pow (by unfold Mdim; omega)
    · rw [e, sub_self] at h2
      exact h2 (zero_pow (by omega))
  · exact absurd rfl hq

theorem lintegral_weight_smul {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {J J' : MatKR k r → (Wq →L[ℂ] Wp)} {η : ℂ} (h : ∀ γ ∈ UH (Hpk k r), J γ = η • J' γ) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J (bigCell k r q.1 (μsec q.2)))) =
      ENNReal.ofReal (‖η‖ ^ 2) * ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J' (bigCell k r q.1 (μsec q.2)))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  by_cases hq : bcWeight k r (Tz k r z) (Tz k r z') q = 0
  · simp [hq]
  · rw [h _ (bigCell_mem_of_weight hk hs hq), hsNormSq_smul, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]

end GlobalTheory.Amp.OpenCellNorm
