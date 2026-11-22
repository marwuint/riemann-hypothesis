import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.SatakeDualWeyl.StatementC

open NumberField IntermediateField Ideal IsDedekindDomain
open scoped Pointwise TensorProduct

noncomputable section

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

def PrincipalStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b c = cc e →
  ∀ 𝔭₂ 𝔭q : Ideal (𝓞 (KinE ζ a b)), 𝔭₂.IsPrime → 𝔭q.IsPrime →
    ((2 : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ → ((q : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭q →
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (c • 𝔟) ∧
      (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟 →
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) ∧
      𝔟 ⊔ c • 𝔟 = ⊤ ∧
      (∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ ∈ Psi e → σ • 𝔟 = 𝔟) ∧
      ∀ 𝔟' : Ideal (𝓞 (hostE ζ a b)),
        differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟' * (c • 𝔟') →
        (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟' →
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) →
        𝔟' = 𝔟

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
