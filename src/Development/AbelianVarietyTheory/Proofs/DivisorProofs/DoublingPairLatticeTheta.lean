import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalInStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblUnitaryBox

section Meas

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance (priority := high) measTup : MeasurableSpace (κ → AF F) := borel _

local instance borelTup : BorelSpace (κ → AF F) := ⟨rfl⟩

theorem integrable_normSq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable (fun x => ‖φ x‖ ^ 2) μ :=
  (schA_memLp_two F κ μ hμ φ hφ).integrable_norm_pow two_ne_zero

theorem lintegral_eq_ofReal (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_normSq μ hμ hφ) (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integral_mul_star_eq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ φ ∈ schA F κ, T φ ∈ schA F κ)
    (hT : ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {φ₁ φ₂ : (κ → AF F) → ℂ}
    (h₁ : φ₁ ∈ schA F κ) (h₂ : φ₂ ∈ schA F κ) :
    ∫ x, T φ₁ x * star (T φ₂ x) ∂μ = ∫ x, φ₁ x * star (φ₂ x) ∂μ := by
  have hn : ∀ φ ∈ schA F κ, ∫ x, ‖T φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := fun φ hφ => by
    have h := hT φ hφ
    rw [lintegral_eq_ofReal μ hμ (hp φ hφ), lintegral_eq_ofReal μ hμ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hm : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∀ c : ℂ, f + c • g ∈ schA F κ := fun f hf g hg c =>
    (schA F κ).add_mem hf ((schA F κ).smul_mem c hg)
  have pol : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∫ x, f x * star (g x) ∂μ =
      (((∫ x, ‖(f + (1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∫ x, ‖(f + (-1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) +
        Complex.I * ((∫ x, ‖(f + Complex.I • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) -
        Complex.I * ((∫ x, ‖(f + (-Complex.I) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ)) / 4 := fun f hf g hg => by
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖(f + c • g) x‖ ^ 2 : ℝ) : ℂ)) μ := fun c =>
      (integrable_normSq μ hμ (hm f hf g hg c)).ofReal
    simp only [← integral_complex_ofReal]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi _) (hi _),
      ← integral_add, ← integral_sub, ← integral_div]
    rotate_left
    · exact ((hi _).sub (hi _)).add ((hi _).const_mul _)
    · exact (hi _).const_mul _
    · exact (hi _).sub (hi _)
    · exact (hi _).const_mul _
    congr 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_add, map_mul,
      map_neg, map_one, Complex.conj_I, Complex.star_def]
    linear_combination ((f x * (starRingEnd ℂ) (g x)) / 2 - (g x * (starRingEnd ℂ) (f x)) / 2) * Complex.I_mul_I
  rw [pol _ (hp _ h₁) _ (hp _ h₂), pol _ h₁ _ h₂]
  simp only [← hn _ (hm _ h₁ _ h₂ _), map_add, map_smul]

end Meas

section Lagr

variable {R A α β m κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype α] [DecidableEq α] [Fintype κ]
  {Bf : Matrix α β A → Matrix α β A → R} (co : Darboux Bf κ)

end Lagr

end GlobalTheory.DblUnitaryBox

end
