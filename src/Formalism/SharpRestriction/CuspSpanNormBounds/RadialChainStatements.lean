import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.ParamsHeightRankConstant

open Matrix MeasureTheory NumberField Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialChainStatements

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat headEl headLt levOf haarOf lenI mid3 wnormSq Msq mm minv mdet psiC psiLow psiUp lowOf upOf
  sdScale muLow muUp stabU muStab IsOrbMeas OmG gTC gZW fNorm)

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

end Formalism.MainNotions.RadialChainStatements

end
