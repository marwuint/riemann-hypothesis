import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeOfHighest
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLe
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModule
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalue
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexifiedDerivedActionLieHomGramAdjointStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevEAddTwo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieUnitaryElementSimpleRoot
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAtStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlProjectionLevelSumSqLe
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameWConjMatrixUnitsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjectorEntryValueUnderLinearFunctional
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacter
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatible
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LoweringBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecomposition

noncomputable section

namespace GlobalTheory.MomOne

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem single_moment_le (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (len : Fin (r + 1) → Ω → ℝ)
    (Ph : Ω → ℝ) (A Rr : ℝ) (hm : ∀ a, AEMeasurable (len a) ν) (hpos : ∀ a, ∀ᵐ x ∂ν, 0 < len a x)
    (hPh : AEMeasurable Ph ν) (h0 : ∀ x, 0 ≤ Ph x) (hmass : ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1) (hA : 0 ≤ A)
    (hR : 1 ≤ Rr)
    (h1 : ∀ q' ≤ (r + 1) * q, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q') * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q'))
    (h2 : ∀ a : Fin r, ∀ q' ≤ (r + 1) * q,
      ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q') * Ph x) ∂ν
        ≤ ENNReal.ofReal (Rr ^ (2 * q'))) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (len a x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ q) := by
  choose l hlm hlp hle using fun a => GlobalTheory.MomentHolder.exists_pos_version ν (len a) (hm a) (hpos a)
  have hall : ∀ᵐ x ∂ν, ∀ a, len a x = l a x := ae_all_iff.2 hle
  set μ : Measure Ω := ν.withDensity fun x => ENNReal.ofReal (Ph x) with hμ
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]⟩
  have hR0 : 0 ≤ Rr := zero_le_one.trans hR
  have hsq : ∀ q : ℕ, Real.sqrt A ^ (2 * q) = A ^ q := fun q => by
    rw [pow_mul, Real.sq_sqrt hA]
  have hup := Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds Ω μ r q l (Real.sqrt A) Rr hlm hlp
    (Real.sqrt_nonneg A) hR0
    (fun q hq => by
      rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0 _ ((hlm 0).pow_const _), hsq]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h1 q hq)
      filter_upwards [hall] with x hx
      rw [hx])
    (fun c q hq => by
      rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0
        (fun ω => (l c.succ ω / l c.castSucc ω) ^ (2 * q)) (((hlm _).div (hlm _)).pow_const _)]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h2 c q hq)
      filter_upwards [hall] with x hx
      rw [hx, hx]) a
  rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0 _ ((hlm a).pow_const _), hsq] at hup
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hup.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hall] with x hx
    rw [hx]
  · rw [mul_pow, ← pow_mul Rr]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR ?_) (by positivity)
    have := Nat.mul_le_mul_left (2 * q) (Nat.lt_succ_iff.1 a.isLt)
    calc 2 * q * a.val ≤ 2 * q * r := this
      _ = 2 * r * q := by ring

variable {k r : ℕ}

theorem lenA_mul_unitary (z : Fin (2 * r + k + 1) → ℂ) (x : Mx k r) {g : Mx k r}
    (hg : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lenA k r z (x * g) a = lenA k r z x a := by
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg
  have h2 : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hg
  have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv h1
  let L : EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    Matrix.toEuclideanLin (star g)
  have hL : ∀ v, WithLp.toLp 2 (star g *ᵥ v) = L (WithLp.toLp 2 v) := fun v => rfl
  have hiso : Isometry L := by
    refine AddMonoidHomClass.isometry_of_norm L ((LinearMap.norm_map_iff_inner_map_map L).2 fun v w => ?_)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    show (star g *ᵥ w.ofLp) ⬝ᵥ star (star g *ᵥ v.ofLp) = _
    rw [Matrix.star_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, star_star, h2, Matrix.vecMul_one, dotProduct_comm]
  unfold lenA
  simp only [Matrix.mul_inv_rev, hinv, ← Matrix.mulVec_mulVec, hL]
  rw [← Set.image_image L, ← Submodule.map_span, Submodule.map_coe, Metric.infDist_image hiso]

theorem lintegral_rmul {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ)
    (hF : ContinuousOn F (GG k r)) (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, ENNReal.ofReal (F (Matrix.of x * g)) ∂νq = ∫⁻ x, ENNReal.ofReal (F (Matrix.of x)) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) A := hF
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hm.ennreal_ofReal (fun s hs x hx => by
    rw [hval x hx]
    exact congrArg ENNReal.ofReal
      ((hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx))) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => congrArg ENNReal.ofReal (hval x hx))))
  exact congrArg ENNReal.ofReal (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem conj_back {ε : Fin (2 * r + k + 1) → Bool} {Q g : Mx k r} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hg : g ∈ PI.UpqRep.Kset ε) :
    Q⁻¹ * g * Q ∈ GG k r ∧ Q⁻¹ * g * Q ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
  have q1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ.2
  have q2 : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hQ.2
  have qi : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have hJ : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := GlobalTheory.CayleyChoice.Kset_sub hg
  have hH : Qᴴ * PI.UpqRep.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  rw [qi]
  refine ⟨?_, Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hQ.2) hg.1) hQ.2⟩
  show (Qᴴ * g * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qᴴ * g * Q) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hH]
  calc (Qᴴ * g * Q)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q) * (Qᴴ * g * Q)
      = Qᴴ * (gᴴ * (Q * Qᴴ) * PI.UpqRep.Jm ε * (Q * Qᴴ) * g) * Q := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [q2, Matrix.mul_one, Matrix.mul_one, hJ]

theorem norm_sq_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (t : ℝ) (q : ℕ) {d : ℝ}
    (hd : 0 ≤ d) (v : Wp) : ‖((t ^ q * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t ^ (2 * q) * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hd]
  ring

end prelim

end GlobalTheory.MomOne
