import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepFirstVariable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepSecondVariable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionsBiThetaTwoVariablesCommute
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIteratedWeilActionBiTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem biAct_all : ∀ D : D7, BiAct D := by
  intro D ψ A S A' χA χS χS' χA' oma omb ha hb C hC
  exact ⟨_root_.GlobalTheory.BiTransfer.isBiTheta_act_left D ψ A S A' χA χS oma ha C hC, _root_.GlobalTheory.BiActRight.isBiTheta_act_right D ψ A S A' χS' χA' omb hb C hC,
    _root_.GlobalTheory.SeeSawComm.comm D ψ A S A' χA χS χS' χA' oma omb ha hb C hC, _root_.GlobalTheory.BiActCont.continuous_biAct D ψ A S A' χA χS χS' χA' oma omb ha hb C hC⟩

end GlobalTheory.SeeSaw
