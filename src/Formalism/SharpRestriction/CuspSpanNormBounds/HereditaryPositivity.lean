import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.HereditaryPositivity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat lenI mid3 wnormSq)

abbrev GM := ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r

end Formalism.MainNotions.HereditaryPositivity

end
