import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.WittLeviObjects
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ChangeOfVariables
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DetNorm

noncomputable section

namespace PI.IwaMeasEx

open MeasureTheory NumberField Matrix
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

section Sizes

variable {I : AutInst} {J : ℕ}

open Classical in

def tBlk (Fr : WittFrame I J) (c : Composition J) (m : I.GA) (i : Fin c.length) : ℝ :=
  (if h : IsUnit (Fr.blkF c m i).det then Formalism.L2.S.S7.GLOne.nrmF I h.unit else 0) *
    ∏ v, ‖(Fr.blkV c m v i).det‖ ^ 2

def eExp (I : AutInst) (c : Composition J) : Fin c.length → ℝ := fun i => 2 * (c.blocksFun i : ℝ) * I.f

def dInv (Fr : WittFrame I J) (c : Composition J) (m : I.GA) : ℝ :=
  cn_dens c.blocksFun (I.n - 2 * J) I.f (chv (eExp I c) (tBlk Fr c m))

end Sizes

end PI.IwaMeasEx

namespace PI.IwaFinBase

end PI.IwaFinBase

end
