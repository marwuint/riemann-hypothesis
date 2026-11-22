import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PCutoffs
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyC2PullbackOfSection
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Imports
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.BigLineBundleMoriwaki
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RingKrullDimLocalizationInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountMonoLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexMinimalPrimesContract
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIndependentModBaseChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSTopPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSeparation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNormalLocusRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProvConj

open MeasureTheory _root_.Metric Filter Topology
open ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Regular hiding le_tmax tmax_le
open GroundTheory.Heights₂.Heights.LowerBoundFree ReciprocityTheory.ChartRestriction.G.Geo

section Points

open MvPolynomial GroundTheory.Heights₂.Heights.Targets.LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_scaled_eq_zero (y : (Σ k, ι k) → Ω) (T : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, ι k => y p * T p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h : ∀ f : MRing ι, aeval (fun p : Σ k, ι k => y p * T p.1) f = eval T (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  rw [h, h0, map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem y_ne_of_X_notMem (y : (Σ k, ι k) → Ω) {p : Σ k, ι k} (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

theorem exists_bound (F : MRing ι) : ∃ M : ℕ, ∀ M', M ≤ M' → ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M' := by
  classical
  refine ⟨∑ m ∈ F.support, ∑ p, m p, fun M' hM' m hm k => le_trans ?_ hM'⟩
  calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
        Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ = ∑ p, m p := (Fintype.sum_sigma _).symm
    _ ≤ _ := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm

theorem valAt_ne_zero {y : (Σ k, ι k) → Ω} {p : ℕ} (hp : p ≠ 0) {b : K → ℤ} {f g : MRing ι}
    (h : IsVerticalDivisorAt (mCoordIdeal y) p b f g) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hP : IsMultiHomogIdeal (mCoordIdeal y)) :
    valAt y (aeval y f / aeval y g * chartMono y c (-b)) z ≠ 0 := by
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_of_X_notMem y fun hX => hc k (by simpa using hz.2 _ hX)
  set z' : (Σ k, ι k) → ℂ := fun q => (z ⟨q.1, c q.1⟩)⁻¹ * z q with hz'
  set y' : (Σ k, ι k) → Ω := fun q => y q * (y ⟨q.1, c q.1⟩)⁻¹ with hy'
  have hz'P : z' ∈ mcPts (mCoordIdeal y) :=
    mcPts_smul hP (fun k => (z ⟨k, c k⟩)⁻¹) (fun k => inv_ne_zero (hc k)) hz
  have hz1 : ∀ k, z' ⟨k, c k⟩ = 1 := fun k => inv_mul_cancel₀ (hc k)
  have hy1 : ∀ k, y' ⟨k, c k⟩ = 1 := fun k => mul_inv_cancel₀ (hyc k)
  obtain ⟨u, v, hu, hv, huv⟩ := h.unit_off_fibre (RingHom.ker (aeval z' : MRing ι →ₐ[ℤ] ℂ)) (RingHom.ker_isPrime _)
    (fun a ha => by rw [RingHom.mem_ker, ← eval_map_int]; exact hz'P.2 a ha)
    (fun k => ⟨c k, by simp [RingHom.mem_ker, hz1]⟩) (by simpa [RingHom.mem_ker] using hp)
  rw [RingHom.mem_ker] at hu hv
  obtain ⟨Mu, hMu⟩ := exists_bound u
  obtain ⟨Mv, hMv⟩ := exists_bound v
  have hU := homogAt_isMultiHomog c (Mu + Mv) u (hMu _ (by omega))
  have hV := homogAt_isMultiHomog c (Mu + Mv) v (hMv _ (by omega))
  have sy : ∀ q : Σ k, ι k, y q = y ⟨q.1, c q.1⟩ * y' q := fun q => by
    simp only [hy']; field_simp [hyc q.1]
  have sz : ∀ q : Σ k, ι k, z q = z ⟨q.1, c q.1⟩ * z' q := fun q => by
    simp only [hz']; field_simp [hc q.1]
  have eU := aeval_scale hU (fun k => z ⟨k, c k⟩) z' z sz
  have eV := aeval_scale hV (fun k => z ⟨k, c k⟩) z' z sz
  have eU' := aeval_scale hU (fun k => y ⟨k, c k⟩) y' y sy
  have eV' := aeval_scale hV (fun k => y ⟨k, c k⟩) y' y sy
  rw [aeval_homogAt c _ _ _ hz1] at eU eV
  rw [aeval_homogAt c _ _ _ hy1] at eU' eV'
  have hzp : (∏ k, z ⟨k, c k⟩ ^ (Mu + Mv)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hUz : aeval z (homogAt c (Mu + Mv) u) ≠ 0 := by rw [eU]; exact mul_ne_zero hzp hu
  have hVz : aeval z (homogAt c (Mu + Mv) v) ≠ 0 := by rw [eV]; exact mul_ne_zero hzp hv
  have hUy : aeval y (homogAt c (Mu + Mv) u) ≠ 0 := fun h0 =>
    hUz (by rw [← eval_map_int]; exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hU h0))
  obtain ⟨bf, bg, hf, hg, hb⟩ := h.degrees
  have hgy : aeval y g ≠ 0 := fun h0 => h.den_not_mem (mem_mCoordIdeal_of_aeval_eq_zero y hg h0)
  have ef := aeval_scale hf (fun k => y ⟨k, c k⟩) y' y sy
  have eg := aeval_scale hg (fun k => y ⟨k, c k⟩) y' y sy
  have e0 : aeval y' (u * f - v * g) = 0 := aeval_scaled_eq_zero y (fun k => (y ⟨k, c k⟩)⁻¹) huv
  rw [map_sub, map_mul, map_mul] at e0
  have hm : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k := by
    rw [chartMono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← hb]
    congr 1
    simp
  have hval : IsValueAt y (aeval y f / aeval y g * chartMono y c (-b)) z
      (eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) v)) /
        eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) u))) := by
    refine ⟨_, _, _, hV, hU, hUy, ?_, by rwa [eval_map_int], rfl⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hgy, eU', eV', ef, eg, ← hm]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ (Mu + Mv)) * chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k) * e0
  rw [valAt_eq hz hval, eval_map_int, eval_map_int]
  exact div_ne_zero hVz hUz

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

end Points

end GlobalTheory.CompanionTheory.Ar.ProvConj

namespace GlobalTheory.CompanionTheory.Ar.ProvParts

end GlobalTheory.CompanionTheory.Ar.ProvParts
