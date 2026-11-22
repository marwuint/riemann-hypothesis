import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidValOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevOfMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainXOfStepXLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriods
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem mainX_of_lawsX (hR : GlobalTheory.Published.CuspRapidDecay) (hH : GlobalTheory.Published.HarishChandraModules) :
    ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  intro D c 𝒯 t L
  have hTwo : TwoX t :=
    _root_.GlobalTheory.SeeSaw.twoX_of_laws D c 𝒯 t (_root_.GlobalTheory.SeeSaw.biAct_all D) (_root_.GlobalTheory.SeeSaw.CenFockPf.cenFock D) (GlobalTheory.SeeSaw.LiftSumProof.liftSum D)
      L.com L.tup L.real L.ker L.rd
  have hRap : RapidVal D := GlobalTheory.SeeSaw.rapidVal_of_cuspRapidDecay hR D
  have hStep : StepX t :=
    _root_.GlobalTheory.SeeSawStep.stepX_of_laws hH D c 𝒯 t (_root_.GlobalTheory.Unf.doubleStep_of_descent D (GlobalTheory.Desc.weil_data_descend D)) hRap
      (GlobalTheory.ValMoveProof.valMove D) (GlobalTheory.SeeSaw.perSum_all D) L.com L.tup L.loc L.val hTwo L.rd
  have hLast : LastX t :=
    _root_.GlobalTheory.SeeSaw.lastX_of_laws hH D c 𝒯 t hRap L.com L.tup L.last hTwo L.per L.rd
  exact GlobalTheory.SeeSaw.mainX_of_stepX_lastX D c 𝒯 t L.tup hStep hLast

end GlobalTheory.SeeSaw
