import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK

open Matrix MeasureTheory NumberField Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BlockEstimateTheorem

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat lenI mid3 wnormSq Msq mm minv mdet psiC psiLow psiUp lowOf upOf sdScale muLow muUp stabU
  muStab IsOrbMeas IsOrbMeasLU OmG gTC gZW fNorm IsKFinCoefT)

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def vmOf (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) : ValMap D.R.k D.R.rS :=
  hk ▸ G.toValMap

end Formalism.MainNotions.BlockEstimateTheorem

end
