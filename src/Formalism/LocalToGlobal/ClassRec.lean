import Formalism.LocalToGlobal.ClassS
import Formalism.LocalToGlobal.ClassSK
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
import Formalism.LocalToGlobal.RatioJoints.CharacterProductEqOne
import Formalism.LocalToGlobal.UnitaryNorms.DatumS
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure RecT (ex : Extra D L hT Gi Gl K Y cX) where

  T : TiedDataSK ex

  pin : Rows.RowPinMin T

  joints : JointsS T.toTiedDataS

  host : HostDatumS T.toTiedDataS

  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W

end

end Formalism.L2
