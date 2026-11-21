import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTLower
import Formalism.LocalRingCardinality.FactDelDualNabla
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Formalism.GradedWeylDivisibility.FinalC

noncomputable section

namespace Formalism.L2.DIV.BrJ

open Formalism.BasicNotions Formalism.MainNotions

theorem branching_interlacing_pairs : PrimeDegreeVariant.Conclusion6 := by
  intro n N h lam sg hI
  exact _root_.gTLower_of Formalism.BasicNotions.factDelDualNabla n N h lam sg hI

variable {D : D7} {u : D.what₂.Word}

variable {D : D7} {u : D.what₂.Word}

end Formalism.L2.DIV.BrJ
