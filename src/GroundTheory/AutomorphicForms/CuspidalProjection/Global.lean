import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import GroundTheory.AutomorphicForms.CuspidalProjection.ContinuousFiniteAdeleSingleAdd
import GroundTheory.AutomorphicForms.RealIwasawaIntegration

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalProjection

open Reduction AutomorphicForm CuspidalSpectrum RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem constantTermL2_unipotent_mul (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (r : ℕ)
    (Y : UPos n r → 𝔸[K]) (z : normOneGL K n) :
    constantTermL2 μ r φ (unipOne K n r Y * z) = constantTermL2 μ r φ z := by
  simp only [constantTermL2, ctFun]
  have h : ∀ X, unipOne K n r X * (unipOne K n r Y * z) = unipOne K n r (X + Y) * z := by
    intro X
    rw [unipOne_add, mul_assoc]
  simp_rw [h]
  refine setIntegral_add_right_of_periodic isAddFundamentalDomain_unipFundamentalDomain
    (h := fun X => (φ : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ (unipOne K n r X * z))) (fun ξ hξ s => ?_) Y
  show (φ : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ (unipOne K n r (ξ + s) * z)) = φ (mk Γ₁ (unipOne K n r s * z))
  rw [unipOne_add, mul_assoc, mk_mul_of_mem (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]

variable (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
  [BorelSpace (v.adicCompletion K)]

variable {μ v}

def ccStar (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    CompactlySupportedContinuousMap (normOneGL K n) ℂ where
  toFun g := conj (f g⁻¹)
  continuous_toFun := Complex.continuous_conj.comp (f.continuous.comp continuous_inv)
  hasCompactSupport' :=
    (f.hasCompactSupport.comp_isClosedEmbedding (Homeomorph.inv (normOneGL K n)).isClosedEmbedding).comp_left
      (map_zero _)

@[simp] theorem ccStar_apply (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (g : normOneGL K n) : ccStar f g = conj (f g⁻¹) := rfl

variable (μ) in

theorem ccToL1_ccStar [μ.IsInvInvariant] (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    UnitaryRep.ccToL1 μ (ccStar f) = UnitaryRep.involution μ (UnitaryRep.ccToL1 μ f) := by
  have h1 : (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) =ᵐ[μ] f :=
    MemLp.coeFn_toLp _
  have h1' : (fun g => (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) g⁻¹) =ᵐ[μ] fun g => f g⁻¹ :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq_comp h1
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (μ := μ) ((ccStar f).continuous.memLp_of_hasCompactSupport
    (ccStar f).hasCompactSupport), UnitaryRep.coeFn_involution μ (UnitaryRep.ccToL1 μ f), h1']
    with g ha hb hc
  rw [hb, hc]
  exact ha

end CuspidalProjection

end

end GroundTheory.Automorphic
