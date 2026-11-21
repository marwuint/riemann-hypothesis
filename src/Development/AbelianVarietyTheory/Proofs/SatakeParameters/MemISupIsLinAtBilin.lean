import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaLoc

open GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}

theorem isLinAt_comp {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    (ι : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ) (hP : ∀ Φ, P (ι Φ))
    (h : IsLinAt ω₁ s μ η ι) : IsLinAt ω₂ s μ η (T ∘ₗ ι) := by
  obtain ⟨c, hc, hc', hι⟩ := h
  refine ⟨c, hc, hc', fun h g hh hg Φ Φ' hΦ => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [← hT _ _ (hP Φ), hι h g hh hg Φ Φ' hΦ, map_smul]

end GlobalTheory.ThetaLoc

end
