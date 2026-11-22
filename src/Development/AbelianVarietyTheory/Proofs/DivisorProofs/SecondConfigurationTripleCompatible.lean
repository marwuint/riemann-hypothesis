import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_mem_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ v, φ v ∈ SB _) (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) : pure f φ ∈ schA F _ := by
  have h3 := (h2.and hM.std).mono fun w hw => hw.1.trans hw.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def schrLin {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ := schr ψ w Φ
  map_add' Φ Ψ := by funext x; simp [schr, mul_add]
  map_smul' c Φ := by funext x; simp [schr]; ring

theorem schrLin_apply {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) : schrLin ψ w Φ = schr ψ w Φ := rfl

theorem schr_mem_schA {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have : schA F κ ≤ (schA F κ).comap (schrLin ψ w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
    show schrLin ψ w (pureA F f g) ∈ schA F κ
    rw [schrLin_apply, hT]
    exact Submodule.subset_span ⟨T f, g', hg', rfl⟩
  exact this hΦ

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

end GlobalTheory.ConeMeasV
