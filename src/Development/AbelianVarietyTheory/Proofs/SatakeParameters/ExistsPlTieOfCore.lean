import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.GO

def primeUnder {E : Type} [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 E) :=
  Q.comap (MulSemiringAction.toRingHom (E ≃ₐ[ℚ] E) (𝓞 E) g) fun x => ⟨g⁻¹ • x, by simp⟩

theorem mem_primeUnder {E : Type} [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    x ∈ (primeUnder g Q).asIdeal ↔ g • x ∈ Q.asIdeal := Iff.rfl

end GlobalTheory.GO
