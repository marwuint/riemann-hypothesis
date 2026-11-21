import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WittStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.WittStatement : StWitt := by
  exact @GlobalTheory.CompanionTheory.FlWitt.stWitt
