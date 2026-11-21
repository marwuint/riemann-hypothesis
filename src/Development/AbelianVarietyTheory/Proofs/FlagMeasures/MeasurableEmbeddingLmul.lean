import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchur

theorem fdegHC_pos {n : ℕ} {mu : Fin n → ℝ} (h : StrictAnti mu) : 0 < Formalism.QuantumDeterminants.fdegHC mu := by
  unfold Formalism.QuantumDeterminants.fdegHC
  refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
  · have := h (Finset.mem_filter.1 hb).2
    exact abs_pos.2 (sub_ne_zero.2 this.ne')
  · have : (a : ℕ) < b := (Finset.mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
    linarith

theorem measurableEmbedding_lmul {k r : ℕ} {t : MatKR k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (fun x : Mt k r => (fun i j => (t⁻¹ * Matrix.of x) i j : Mt k r)) := by
  have hc : ∀ s : MatKR k r, Continuous (fun x : Mt k r => (fun i j => (s * Matrix.of x) i j : Mt k r)) := fun s => by
    have h1 : Continuous (fun x : Mt k r => (Matrix.of x : MatKR k r)) := continuous_id
    exact continuous_const.matrix_mul h1
  let e : Mt k r ≃ᵐ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => by
        show t * (t⁻¹ * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
      right_inv := fun x => by
        show t⁻¹ * (t * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
      measurable_toFun := (hc _).measurable
      measurable_invFun := (hc _).measurable }
  exact e.measurableEmbedding

theorem isBesselMapSm_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp} (h : IsBesselMapSm z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW σ w v := fun w v => by
    induction w with
    | nil => rfl
    | cons X w ih => exact congrArg (dsig σ X) ih
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simpa only [e] using h5 v hv

theorem theta_pos (D : D7) {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hv : 0 ≤ D.host.v) (hW : GoodW D τ w w' θ W) : 0 < θ := by
  by_contra hθ
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, q1, -⟩ := hW
  have hk : kapN D θ = 0 :=
    ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _) (not_lt.1 hθ))
  have hN0 : W.μN = 0 := by rw [hN, hk]; unfold haarLie; exact zero_smul _ _
  have h1 := q1 (fun _ => 1) measurable_const
  rw [hN0] at h1
  simp only [muS, Measure.prod_zero, Measure.map_zero, lintegral_const, one_mul, Measure.coe_zero,
    Pi.zero_apply, zero_mul] at h1
  exact hG.2.1 (Measure.measure_univ_eq_zero.1 h1)

end GlobalTheory.BesselSchur
