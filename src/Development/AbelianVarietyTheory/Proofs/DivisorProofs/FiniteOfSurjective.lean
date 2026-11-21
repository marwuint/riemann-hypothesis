import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceUnitsBasisOfNbhds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadicStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.CentTorus
open scoped TensorProduct

namespace GlobalTheory.CentTorus.ClassSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

def tmap (π : A →ₐ[ℚ] B) : L ⊗[ℚ] A →ₐ[ℚ] B ⊗[ℚ] L :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeLeft.comp π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tmap_tmul (π : A →ₐ[ℚ] B) (l : L) (a : A) : tmap π (l ⊗ₜ[ℚ] a) = π a ⊗ₜ[ℚ] l := by
  simp [tmap]

end Tmap

end GlobalTheory.CentTorus.ClassSplit

namespace GlobalTheory.CentTorus.ClassSplit

end GlobalTheory.CentTorus.ClassSplit

namespace GlobalTheory.CentTorus.ClassSplit

end GlobalTheory.CentTorus.ClassSplit

