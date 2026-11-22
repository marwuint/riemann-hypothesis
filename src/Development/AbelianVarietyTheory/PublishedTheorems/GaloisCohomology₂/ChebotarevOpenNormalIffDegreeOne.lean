import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

def ChebotarevOpenNormal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → U.Normal →
    ∀ (g : G F Ω) (A : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ v : HeightOneSpectrum (𝓞 F), v ∉ A ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
        ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ U ∧
          ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ U

end GlobalTheory.Published

end
