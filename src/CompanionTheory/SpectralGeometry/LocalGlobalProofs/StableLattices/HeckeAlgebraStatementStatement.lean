import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeAlgebraStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeAlgebraTheorem : StHecke := by
  exact @GlobalTheory.CompanionTheory.HeckeBern.stHecke
