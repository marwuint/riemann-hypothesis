import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.CcModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem realM_mt {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hth : IsInfEmb τ th) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W th h := by
  have e : θ hτ.choose = th :=
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ _ _ (by have := hθ hτ.choose; rwa [← hτ.choose_spec] at this) hth
  rw [realM, dif_pos hτ, compAt, e]
  rfl

theorem exists_atComp {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hΨ : ∀ k, ∀ τ ∈ (U.X k).Ψ, ∃ ρ, τ = tauE D ρ)
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hD : DictLat U W hr dict ι e F ik φ th x₀) (h : GA D W) :
    ∃ γ, AtComp θ W hr U.X dict x₀ h γ := by
  obtain ⟨γ, hγ, h1, -, h3⟩ := hD.2 h
  refine ⟨γ, hγ, ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [h1, latR, Submodule.map_coe]
    rfl
  · funext τ
    have := h3 τ
    rw [← realM_mt hθ W (γ * h) τ.1 (hΨ _ _ τ.2) _ (hth _ τ)] at this
    exact this

variable {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc cc' : U.Comp → ℂ}

end

end GlobalTheory.AdTh.CcModel
