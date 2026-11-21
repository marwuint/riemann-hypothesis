import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open MeasureTheory

namespace GlobalTheory

section
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H}

omit [μ.IsMulLeftInvariant] [Countable Γ] in

theorem isFundamentalDomain_image_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) '' 𝓕) μ := by
  refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
  · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
  · intro γ h
    simp [Subgroup.smul_def, mul_assoc]

theorem setIntegral_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  rw [h𝓕.setIntegral_eq (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)]
  exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
    (measurableEmbedding_mulRight y) u 𝓕).symm

theorem integrableOn_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  rw [h𝓕.integrableOn_iff (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)] at hi
  exact ((measurePreserving_mul_right μ y).integrableOn_image
    (measurableEmbedding_mulRight y)).1 hi

end

end GlobalTheory
