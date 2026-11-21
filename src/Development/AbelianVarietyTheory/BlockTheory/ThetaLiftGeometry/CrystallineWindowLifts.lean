import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW

variable (D : D7)

def InertInK (l : ℕ) : Prop := D.host.cls l = .signal ∨ D.host.cls l = .inertClass

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts
