import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.Chain.LiftReg

theorem liftProps_obj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D :=
  fun hP D => liftProps_of_rapidDecay hP D (_root_.GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D)

end GlobalTheory.Chain.LiftReg
