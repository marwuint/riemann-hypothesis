import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.GModel
variable {D : D7} {c : Comm D} {v : VCom c}

open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {D : _root_.Formalism.BasicNotions.D7} {c : _root_.GlobalTheory.SeeSaw.Comm D} {v : _root_.GlobalTheory.SeeSaw.VCom c} in

theorem _root_.GlobalTheory.SeeSaw.GModel.phi_sb (G : _root_.GlobalTheory.SeeSaw.GLoc v) :
    (∀ j a H, (G.S.T (Fin D.R.t)).Phi j a H ∈
      _root_.GlobalTheory.SplitWeil.SB _) ∧
    (G.S.T (Fin D.R.t)).PhiTop ∈ _root_.GlobalTheory.SplitWeil.SB _ := by
  have hreg : (G.S.T (Fin D.R.t)).Regular := by
    unfold _root_.GlobalTheory.SymChain.SymData.T _root_.GlobalTheory.StepData.typeChain
    exact _root_.GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
  obtain ⟨hstep, htop, -⟩ := hreg
  exact ⟨hstep, htop⟩

end GlobalTheory.SeeSaw.GModel
end
