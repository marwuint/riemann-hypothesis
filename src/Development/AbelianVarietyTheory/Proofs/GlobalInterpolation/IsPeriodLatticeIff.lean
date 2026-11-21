import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitPosMeanOfPositivePart
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReduced
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPeriodElement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormThetaCharTermLe

noncomputable section

namespace GlobalTheory.Theta0MeanProof

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
open scoped nonZeroDivisors

theorem lemA : ∀ (D : D7) (c : Ideal (𝓞 D.host.K)), c ≠ ⊥ → ∀ x : ℂ, x ≠ 0 →
    (∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x) ∧
    ∃ ω₁ τ : ℂ, ω₁ ≠ 0 ∧ 0 < τ.im ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D c x) ω₁ τ ∧
      1 / 2 ≤ τ.im ∧ 2 * τ.im ≤ Real.sqrt D.host.d := GlobalTheory.IdealLattice.main

theorem lemD : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im →
    ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀ := GlobalTheory.Glob.EvenThetaBound.evenThetaConst_bounded

theorem isPeriodLattice_iff {Λ : AddSubgroup ℂ} {ω₁ τ : ℂ} :
    JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ τ ↔ Λ = PeriodLatticeAgreement.latt ω₁ τ := by
  constructor
  · intro h; ext x; exact (h x).trans PeriodLatticeAgreement.mem_latt.symm
  · rintro rfl x; exact PeriodLatticeAgreement.mem_latt

theorem log_normSq {Λ : AddSubgroup ℂ} {τ t : ℂ} {a b : Fin 2}
    (hpos : 0 < normSq1 Λ (th0 Λ t)) (hτ : 0 < τ.im)
    (hf : (normSq1 Λ (th0 Λ t))⁻¹ = Real.sqrt (2 * τ.im) * ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ^ 2) :
    0 < ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ∧ Real.log (normSq1 Λ (th0 Λ t)) =
      -(1 / 2) * Real.log 2 - (1 / 2) * Real.log τ.im - 2 * Real.log ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ := by
  set N := normSq1 Λ (th0 Λ t)
  set th := ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖
  have hs : 0 < Real.sqrt (2 * τ.im) := Real.sqrt_pos.2 (by linarith)
  have hth : 0 < th := by
    have h1 : 0 < Real.sqrt (2 * τ.im) * th ^ 2 := hf ▸ inv_pos.2 hpos
    have h2 : 0 < th ^ 2 := pos_of_mul_pos_right h1 hs.le
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at h2; simp at h2)
  refine ⟨hth, ?_⟩
  have e1 : Real.log N = -Real.log N⁻¹ := by rw [Real.log_inv]; ring
  rw [e1, hf, Real.log_mul hs.ne' (by positivity), Real.log_sqrt (by linarith), Real.log_mul (by norm_num) hτ.ne',
    Real.log_pow]
  push_cast; ring

theorem log_area {Λ : AddSubgroup ℂ} {ω₁ τ : ℂ} (hP : PeriodLatticeAgreement.LatticePeriodEta) (hω : ω₁ ≠ 0) (hτ : 0 < τ.im)
    (hL : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ τ) (hd : discr Λ = 1) :
    0 < ‖ModularForm.eta τ‖ ∧ Real.log (area Λ) =
      Real.log 4 + 2 * Real.log Real.pi + Real.log τ.im + 4 * Real.log ‖ModularForm.eta τ‖ := by
  rw [isPeriodLattice_iff] at hL
  subst hL
  have he : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  have hen : 0 < ‖ModularForm.eta τ‖ := norm_pos_iff.2 he
  refine ⟨hen, ?_⟩
  have h := hP.2.2.1 ω₁ ⟨τ, hτ⟩ hω
  simp only [PeriodLatticeAgreement.period, hd, norm_one, Real.one_rpow, one_mul] at h
  change area (PeriodLatticeAgreement.latt ω₁ τ) / Real.pi = 4 * Real.pi * τ.im * ‖ModularForm.eta τ‖ ^ 4 at h
  have hpi := Real.pi_pos
  have h2 : area (PeriodLatticeAgreement.latt ω₁ τ) = 4 * Real.pi ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 := by
    field_simp at h; linarith
  rw [h2, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hτ.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
  push_cast; ring

theorem sum_log_nonneg (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (X : M) (hX : X ≠ 0)
    (hXi : IsIntegral ℤ (X : ℂ)) : 0 ≤ ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ X‖ := by
  haveI : NumberField M := ⟨⟩
  have hXi' : IsIntegral ℤ X := by
    have : IsIntegral ℤ ((M.val : M →ₐ[ℚ] ℂ) X) := hXi
    exact (isIntegral_algHom_iff ((M.val : M →ₐ[ℚ] ℂ).restrictScalars ℤ) M.val.injective).1 this
  have h := Formalism.HermitianLattices.IntegralLatticeDensity.integer_mean_log_bound M ⟨X, hXi'⟩ (by
    intro h0; apply hX; exact congrArg Subtype.val h0)
  rw [← (RingHom.equivRatAlgHom M ℂ).sum_comp]
  exact h

theorem log_sqrt_le_log_v (D : D7) : Real.log (Real.sqrt D.host.d) ≤ Real.log D.host.v := by
  have h1 := GlobalTheory.Theta0MeanCompare.two_sqrt_le_rd D
  have h2 := GlobalTheory.Theta0MeanCompare.one_le_sqrt_d D
  exact Real.log_le_log (by linarith) (by unfold Host.v; linarith)

theorem half_le_log_v (D : D7) : 1 / 2 ≤ Real.log D.host.v := by
  have h7 : (4 : ℝ) ≤ D.host.d := by
    have := D.host.hyp.2.2.2.1
    exact_mod_cast (by omega : 4 ≤ D.host.d)
  have hs : (2 : ℝ) ≤ Real.sqrt D.host.d := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h7
  have h1 := log_sqrt_le_log_v D
  have h2 : Real.log 2 ≤ Real.log (Real.sqrt D.host.d) := Real.log_le_log (by norm_num) hs
  have := Real.log_two_gt_d9
  linarith

theorem bound_le_half (D : D7) {L : ℝ} (hL : Real.log D.host.v + |logDerivativeAtOne D| ≤ L) :
    SignedLogMeans.bound D ≤ (1 / 2) * L := by
  have h1 := log_sqrt_le_log_v D
  have h2 := le_abs_self (logDerivativeAtOne D)
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  unfold SignedLogMeans.bound
  linarith

theorem log_d_le (D : D7) {L : ℝ} (hL : Real.log D.host.v + |logDerivativeAtOne D| ≤ L) :
    (1 / 4) * Real.log D.host.d ≤ (1 / 2) * L := by
  have h1 := log_sqrt_le_log_v D
  have h2 := abs_nonneg (logDerivativeAtOne D)
  have h4 : Real.log (Real.sqrt (D.host.d : ℝ)) = (1 / 2) * Real.log D.host.d := by
    rw [Real.log_sqrt (by positivity)]; ring
  linarith

end GlobalTheory.Theta0MeanProof
