import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedConjugationDiagOneLiftBlockMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockGlBorderedConjugationActionI
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLeMaxUltra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrand
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PreimageDiagOneGeneralLinearEmbeddingIntegralGLS

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem act_mul' {k : Type} [CommRing k] {n : ℕ} (g h : GL (Fin n) k) (Y : Gl n k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]

theorem omega_lift {F : Type} [NontriviallyNormedField F] (r : ℕ) (Z : Gl r F) (μ l : F) :
    omega (GlobalTheory.JR.Step.lift Z μ l) = omega Z := by
  have h := (GlobalTheory.JR.transfer_factor_lemma F (r + 1)).1 (GlobalTheory.JR.Step.lift Z μ l)
  have hc : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = lastDet Z := rfl
  unfold omega eta
  rw [h, hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem orbG_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  intro F E _ _ _ _ hU r M M' Z μ l hμ hΔ
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨lc1, sc1⟩ := gl_lc_sc F (r + 1)
  letI := M.mG
  haveI := M.bG
  letI := M'.mG
  haveI := M'.bG
  haveI := M.haarG
  haveI := M'.haarG
  haveI := gl_unimodular F E (r + 1) M
  haveI := gl_unimodular F E r M'
  obtain ⟨hO, hC⟩ := _root_.GlobalTheory.JR.GLift.glO_isOpen_isCompact F (r + 1)
  have hemb := GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding F r
  have key := GlobalTheory.CosetIntegral.integral_eq_of_coset_support (GL (Fin (r + 1)) F) (GL (Fin r) F)
    (GlobalTheory.JR.Step.emb r F) hemb M.μG M'.μG (glOSub (r + 1) F) hO hC M.volG
    (by rw [coe_glOSub, _root_.GlobalTheory.JR.GLift.emb_preimage_glO F r]; exact M'.volG)
    (fun g => unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) * omega (act g (GlobalTheory.JR.Step.lift Z μ l)))
    (fun k hk g => by
      simp only [act_mul', _root_.GlobalTheory.JR.GLift.unitG_act F (r + 1) k hk, _root_.GlobalTheory.JR.omega_act_glO F (r + 1) k hk])
    (fun g hg => _root_.GlobalTheory.JR.GLift.support_lift F E r Z μ l hμ g (left_ne_zero_of_mul hg))
    ((_root_.GlobalTheory.JR.orbG_integrand_hasCompactSupport F (r + 1) _ hΔ).comp_isClosedEmbedding hemb)
  unfold orbG
  rw [key]
  simp only [GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix, _root_.GlobalTheory.JR.UnitGLift.unitG_lift F r _ μ l hμ.le, omega_lift, mul_assoc]
  exact integral_const_mul _ _

end GlobalTheory.JR.GLift
