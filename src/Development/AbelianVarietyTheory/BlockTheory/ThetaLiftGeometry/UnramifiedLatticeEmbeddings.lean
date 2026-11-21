import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW

def InertInK {R : Ranks} (H : Host R) (p : ℕ) : Prop :=
  H.cls p = .signal ∨ H.cls p = .inertClass

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs
