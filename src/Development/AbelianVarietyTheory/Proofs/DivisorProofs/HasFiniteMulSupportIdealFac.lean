import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm

noncomputable section

namespace GlobalTheory.EulerIdeal

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.L2.Host (aboveF)
open scoped nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_count (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w 𝔞 ≠ 0}.Finite :=
  Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)

theorem hasFiniteMulSupport_zpow {M : Type} [DivInvMonoid M] (x : HeightOneSpectrum (𝓞 E) → M)
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    Function.HasFiniteMulSupport fun w => x w ^ FractionalIdeal.count E w 𝔞 :=
  (finite_count 𝔞).subset fun w hw h0 => hw (by simp only [h0, zpow_zero])

theorem idealVal_mul (χ : Chr F E) {𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) (h𝔠 : 𝔠 ≠ 0) :
    idealVal χ (𝔟 * 𝔠) = idealVal χ 𝔟 * idealVal χ 𝔠 := by
  unfold idealVal
  simp only [FractionalIdeal.count_mul E _ h𝔟 h𝔠, zpow_add]
  exact finprod_mul_distrib (hasFiniteMulSupport_zpow _ _) (hasFiniteMulSupport_zpow _ _)

theorem idealVal_inv (χ : Chr F E) (𝔟 : FractionalIdeal (𝓞 E)⁰ E) : idealVal χ 𝔟⁻¹ = (idealVal χ 𝔟)⁻¹ := by
  unfold idealVal
  simp only [FractionalIdeal.count_inv, zpow_neg]
  exact finprod_inv_distrib _

open GlobalTheory.ThK

variable {σ : E →ₐ[F] E}

end GlobalTheory.EulerIdeal
