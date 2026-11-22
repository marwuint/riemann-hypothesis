import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller

noncomputable section

namespace Formalism.MainNotions.FamilyNumericLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Filter Topology

theorem cyl_univ (D : D7) (k : Fin 2) : cyl D k Set.univ = Set.univ := by
  ext t; simp [cyl]

end Formalism.MainNotions.FamilyNumericLemmas
