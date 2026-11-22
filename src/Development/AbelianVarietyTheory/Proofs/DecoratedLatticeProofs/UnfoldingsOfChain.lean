import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfolding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodEvaluationUnfoldingOfWittDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfWeilDatumDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem unfoldings_of_chain :
    ∀ D : D7, UnfBF D ∧ EvalBF D ∧ UnfFB D ∧ DoubleStep D ∧ LastLaw D ∧ IT D ∧ ContrLaw D ∧ SeeLast D := by
  intro D
  have hD : Descent D := _root_.GlobalTheory.Desc.weil_data_descend D
  exact ⟨_root_.GlobalTheory.UnfBessel.unfBF D hD, _root_.GlobalTheory.Unf.evalBF_of_descent D hD, _root_.GlobalTheory.Unf.unfFB_of_descent D hD, _root_.GlobalTheory.Unf.doubleStep_of_descent D hD,
    _root_.GlobalTheory.Unf.LastSteps.lastLaw D, _root_.GlobalTheory.Unf.iteratedUnfolding_of_descent D hD, GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D, _root_.GlobalTheory.SeeLastPf.seeLast D⟩

end GlobalTheory.Unf
