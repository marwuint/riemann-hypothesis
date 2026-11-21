import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerComposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionTheta

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixUniq

open scoped Classical

abbrev ev0 {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem rho_zero_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (z : Matrix (Fin n) (Fin d₁) (AE F E))
    (hz : (M₁.co.e z).1 = 0) (Ψ : Fn F n d₁) : M₁.co.rho ψ z Ψ 0 = Ψ 0 := by
  simp [Darboux.rho, schr, hz]

theorem rho_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (y : Fin n × Fin d₁ → AF F) (Ψ : Fn F n d₁) :
    M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := by
  simp [Darboux.rho, schr]

end GlobalTheory.MixUniq

namespace GlobalTheory.MixUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem apply_eq_evaluation_zero (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (ι' : Matrix (Fin d) (Fin d₁) E)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι')ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ)) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (y : Fin n × Fin d₁ → AF F) :
    S Φ y = ev0 (Fin n × Fin d₁) (S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ)) := by
  rw [hS _ Φ hΦ]
  simp only [ev0, LinearMap.proj_apply]
  rw [rho_first]

theorem evAt_zero_comp_eq_of_exp_phase_mul (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (H' : Plane E d d₁)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ))
    (hI : ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ u Φ) = S Φ)
    (w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hw : ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr ψ w φ = M.co.rho ψ u (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ))
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    (ev0 (Fin n × Fin d₁) ∘ₗ S) (schr ψ w Φ) = (ev0 (Fin n × Fin d₁) ∘ₗ S) Φ := by
  obtain ⟨u, hu, z, hz, he⟩ := hw
  have h1 := GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ hΦ
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI u hu _ h1, hS z Φ hΦ, rho_zero_first M₁ ψ z hz]

end GlobalTheory.MixUniq
