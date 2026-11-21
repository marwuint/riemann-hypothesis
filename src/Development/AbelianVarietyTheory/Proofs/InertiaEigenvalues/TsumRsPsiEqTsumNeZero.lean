import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableInfMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformUniformRapidDecayFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.RSThetaLow

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def rsHat (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  adelicFourierPi E (rsPsi ℓ φ φ' Φ J η g) y

omit [IsTotallyComplex E] in
variable (E a) in

def lowSet : Set (GA E a) := {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}

omit [IsTotallyComplex E] in
theorem continuous_absDet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)

omit [IsTotallyComplex E] in
theorem absDet_invT (g : GA E a) : (ideleModule E (GeneralLinearGroup.det (invT a (Ad E) g)) : ℝ) =
    (ideleModule E (GeneralLinearGroup.det g) : ℝ)⁻¹ := by
  have h : GeneralLinearGroup.det (invT a (Ad E) g) = GeneralLinearGroup.det g⁻¹ := Units.ext (det_transpose _)
  rw [h, map_inv, map_inv]
  rfl

variable {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)

theorem rsPsi_zero (φ φ' : GA E a → ℂ) (hs : tsupport Φ ⊆ rowSet E ℓ) (g : GA E a) : rsPsi ℓ φ φ' Φ J η g 0 = 0 := by
  have h : Φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => hs h (Classical.arbitrary _) rfl
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  simp only [rsPsi, thetaFn, rsInf, e, h, mul_zero, zero_mul]

theorem rsPsi_mem (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    rsPsi ℓ F.1 F'.1 Φ J η g ∈ schwartzBruhatPi E (Fin a) :=
  thetaFn_mem ((isTest_rsInf F F' hΦ g).2.1.toSchwartzMap (isTest_rsInf F F' hΦ g).1) J η

theorem rsHat_eq (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) (y : Fin a → Ad E) :
    rsHat ℓ F.1 F'.1 Φ J η g y =
      infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E (y i)) * (finiteAdelicChar E (∑ i, η i * pFin E (y i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E (y i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ) :=
  adelicFourierPi_thetaFn ((isTest_rsInf F F' hΦ g).2.1.toSchwartzMap (isTest_rsInf F F' hΦ g).1) J η y

theorem stronglyMeasurable_rsHat {F F' : Sm E a} (h : Continuous F.1) (h' : Continuous F'.1)
    (hΦ : IsTest (rowSet E ℓ) Φ) {y : GA E a → Fin a → Ad E} (hy : Continuous y) :
    StronglyMeasurable fun g => rsHat ℓ F.1 F'.1 Φ J η g (y g) := by
  simp only [rsHat_eq J η F F' hΦ]
  have h1 : ∀ i, Continuous fun g => pInf E (y g i) := fun i =>
    continuous_pInf.comp ((continuous_apply i).comp hy)
  have h2 : ∀ i, Continuous fun g => pFin E (y g i) := fun i =>
    (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hy)
  have h3 : Continuous ((latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt _, isOpen_latt _⟩ continuous_const)
  haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance
  have h4 : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ F.1 F'.1 Φ p.1 p.2 *
      (Real.fourierChar (-∑ i, ∑ w, 2 * (p.2 i w * pInf E (y p.1 i) w).re) : ℂ) := by
    refine (continuous_rsInf h h' hΦ.1.continuous hΦ.2.2).mul (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (Continuous.neg (continuous_finset_sum _ fun i _ =>
        continuous_finset_sum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp (Continuous.mul ?_ ?_))))))
    · fun_prop
    · exact (continuous_apply w).comp ((h1 i).comp continuous_fst)
  refine ((h4.stronglyMeasurable.integral_prod_right'.mul (Continuous.stronglyMeasurable ?_)).mul
    (h3.comp (continuous_pi h2)).stronglyMeasurable).mul stronglyMeasurable_const
  exact continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_finset_sum _ fun i _ => continuous_const.mul (h2 i)))

theorem exists_norm_rsHat_le {ι : Type} {S S' : Submodule ℂ (Sm E a)} {g : ι → GA E a} {w : ι → ℝ}
    (hL : ∀ X, ∀ F ∈ S, lie E a X F ∈ S) (hL' : ∀ X, ∀ F ∈ S', lie E a X F ∈ S')
    (hS : ∀ F ∈ S, ∀ C₀ : Set (GA E a), IsCompact C₀ → ∃ C : ℝ, ∀ i, ∀ c ∈ C₀, ‖F.1 (g i * c)‖ ≤ C * w i)
    (hS' : ∀ F ∈ S', ∃ C : ℝ, ∀ x, ‖F.1 x‖ ≤ C) {F F' : Sm E a} (hF : F ∈ S) (hF' : F' ∈ S')
    (hΦ : IsTest (rowSet E ℓ) Φ) (M : ℕ) : ∃ C : ℝ, ∀ i y,
      ‖rsHat ℓ F.1 F'.1 Φ J η (g i) y‖ * (1 + ‖fun j => pInf E (y j)‖) ^ M ≤ C * w i := by
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.fourier_decay_family E a ι w (famSpan ℓ S S' g) (famSpan_bound hS hS')
    (fun f hf => (famSpan_fderiv hL hL' f hf).2) M _ (Submodule.subset_span ⟨F, hF, F', hF', Φ, hΦ, rfl⟩)
  refine ⟨(finiteMeasurePi E (latt a J)).toReal * C, fun i y => ?_⟩
  have h1 := hC i fun j => pInf E (y j)
  have h2 : ‖(latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) fun i => pFin E (y i)‖ ≤ 1 :=
    (norm_indicator_le_norm_self _ _).trans (by simp)
  rw [rsHat_eq J η F F' hΦ, norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm _ (ENNReal.toReal _), mul_assoc, mul_assoc _ C]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ h1) ENNReal.toReal_nonneg
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) h2) (by positivity)

variable {π π' : CuspSub E a} {φ φ' : Sm E a}

theorem poisson_rsPsi (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    Summable (fun ξ : Fin a → E => ‖rsPsi ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)‖) ∧
    Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} =>
      ‖rsHat ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) ∧
    ∑' ξ : Fin a → E, rsPsi ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) =
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ)⁻¹ * (rsHat ℓ F.1 F'.1 Φ J η g 0 +
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          rsHat ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) := by
  obtain ⟨h1, h2, h3⟩ := poisson_vecMul g (rsPsi_mem J η F F' hΦ g)
  refine ⟨h1, h2.subtype _, h3.trans ?_⟩
  rw [Complex.ofReal_inv, ← h2.of_norm.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton 0 fun ξ : Fin a → E =>
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)]
  have e : (fun j => algebraMap E (Ad E) ((0 : Fin a → E) j)) = 0 := funext fun _ => map_zero _
  rw [e, zero_vecMul]
  rfl

theorem tsum_rsPsi_eq_tsum_ne_zero (φ φ' : GA E a → ℂ) (hs : tsupport Φ ⊆ rowSet E ℓ) (g : GA E a) :
    ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) =
      ∑' ξ : Fin a → E, rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := by
  refine tsum_subtype_eq_of_support_subset (s := {ξ | ξ ≠ 0})
    (f := fun ξ : Fin a → E => rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) ?_
  rintro ξ hξ rfl
  have e : (fun j => algebraMap E (Ad E) ((0 : Fin a → E) j)) = 0 := funext fun _ => map_zero _
  exact hξ (by simp only [e, zero_vecMul, rsPsi_zero J η φ φ' hs])

def partA (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ lowSet E a, rsHat ℓ φ φ' Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ

def partB (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
    rsHat ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ

variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}

end GlobalTheory.RSThetaLow
