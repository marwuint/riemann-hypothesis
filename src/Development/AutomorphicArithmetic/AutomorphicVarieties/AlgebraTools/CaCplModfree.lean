import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplQuot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FlatnessPrecompleteProducts

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Algebra Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B]
      (M : Type) [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M] [Module.Flat Λ M],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p →
      Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) :=
  _root_.UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange
