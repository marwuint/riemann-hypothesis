import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MainFin

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J.ChevalleyRestriction

private theorem main_fin (A : Type) [CommRing A] [IsDomain A] (s : Finset A) :
    ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B A],
      Algebra.adjoin B (s : Set A) = ⊤ → Function.Injective (algebraMap B A) →
      ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
        y b ≠ 0 → ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Ra5.main_fin A s

end UpperTheory.V.J.ChevalleyRestriction

theorem UpperTheory.V.J.chev :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
        ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
          ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  intro B A _ _ _ _ _ hft hinj a ha
  obtain ⟨s, hs⟩ := hft.out
  exact UpperTheory.V.J.ChevalleyRestriction.main_fin A s B hs hinj a ha
