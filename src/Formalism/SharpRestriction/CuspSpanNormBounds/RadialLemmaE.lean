import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialRuleConsequences

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat headEl headLt levOf haarOf cutF energy Std lenI mid3 wnormSq IsKFinCoefT)

end Formalism.MainNotions.RadialRuleConsequences
