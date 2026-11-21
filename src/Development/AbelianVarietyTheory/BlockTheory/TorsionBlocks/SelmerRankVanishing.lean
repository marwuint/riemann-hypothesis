import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.Statement
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WeaklyAdmissibleFiltrations.Statement
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions ReciprocityTheory.Gal

namespace GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

def DivMod (A : Type) [CommRing A] [IsDomain A] (n : ℕ) : Type := Fin n → KmodO A

section DivInst

variable (A : Type) [CommRing A] [IsDomain A] (n : ℕ)

instance : AddCommGroup (DivMod A n) := inferInstanceAs (AddCommGroup (Fin n → KmodO A))
instance : Module A (DivMod A n) := inferInstanceAs (Module A (Fin n → KmodO A))
instance : TopologicalSpace (DivMod A n) := ⊥
instance : DiscreteTopology (DivMod A n) := ⟨rfl⟩
instance : IsTopologicalAddGroup (DivMod A n) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

end DivInst

end GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists
