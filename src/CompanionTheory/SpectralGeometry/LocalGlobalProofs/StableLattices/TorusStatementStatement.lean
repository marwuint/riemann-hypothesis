import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TorusStatement : StTor := by
  exact @GlobalTheory.CompanionTheory.FrameTorus.stTor
