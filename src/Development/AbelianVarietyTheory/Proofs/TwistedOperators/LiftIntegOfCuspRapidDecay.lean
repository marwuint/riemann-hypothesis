import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.Chain.LiftConv

theorem liftInteg_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.Chain.LiftInteg D :=
  fun hP D => liftInteg_of_growth hP D (_root_.GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D)

end GlobalTheory.Chain.LiftConv
