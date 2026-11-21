import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MovingStatement : StMove := by
  exact @GlobalTheory.CompanionTheory.CartanMove.stMove
