import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteIntegralsDoubleStepValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem placeLaws_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c)
    (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) →
    (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v 𝒯 t w hc hvl hv ht hp
  refine ⟨fun s => ?_, ?_, ?_⟩
  · exact GlobalTheory.T.locally_finite_of_tuple_conditions D c v (t s) (w s) hc hv (ht s) (hp s).form (hp s).off (hp s).gs (hp s).qfin
  · exact GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value D c v 𝒯 t w hc hv ht hp (GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (_root_.GlobalTheory.SeeSaw.biAct_all D)
  · exact GlobalTheory.T.seeSawLastTwoSteps_doubleLiftPeriod_value D c v 𝒯 t w hc hvl hv ht hp (GlobalTheory.Unf.LastSteps.lastLaw D) (_root_.GlobalTheory.SeeLastPf.seeLast D)
      (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (_root_.GlobalTheory.SeeSaw.biAct_all D)

end GlobalTheory.SeeSaw
