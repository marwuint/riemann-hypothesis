import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Formalism.LandauZeroFreeBounds.Statement
import Formalism.FrobeniusOrbits.Statement

noncomputable section

namespace GlobalTheory.NT

open Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField IsDedekindDomain ArithmeticFunction
open Formalism.HermitianLattices.GL2PrimeSums (Li PP)

def RayField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
        ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
          ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

end GlobalTheory.NT

end
