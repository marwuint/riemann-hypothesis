import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions

theorem latRowLat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatRowLat X u :=
  latRowLat_of LatDictZ.lattice_genus X u

theorem latSurj {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatSurj X u :=
  latSurj_of LatDictZ.anisotropic_vector_orbit X u

theorem lattice_steps_hold : LatticeRowBijectionClassFinite := fun _ X hK u =>
  ⟨latRowLat X u, latSurj X u, latInj X u, Formalism.L2.SG.Closed.ClassFin_holds X u hK⟩

end Formalism.L2.SG.Pf
