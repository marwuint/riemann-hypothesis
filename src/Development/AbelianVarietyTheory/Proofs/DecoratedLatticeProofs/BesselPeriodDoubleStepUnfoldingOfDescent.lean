import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfolding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLink
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLink

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem doubleStep_of_descent : ∀ D : D7, Descent D → DoubleStep D := fun D hD =>
  _root_.GlobalTheory.Unf.doubleStep_of_laws D (_root_.GlobalTheory.UnfBessel.unfBF D hD) (_root_.GlobalTheory.Unf.unfFB_of_descent D hD) (_root_.GlobalTheory.UnfLink.link D) (_root_.GlobalTheory.handFBLaw D) (_root_.GlobalTheory.Unf.Flat.flatLaw D)

end GlobalTheory.Unf
