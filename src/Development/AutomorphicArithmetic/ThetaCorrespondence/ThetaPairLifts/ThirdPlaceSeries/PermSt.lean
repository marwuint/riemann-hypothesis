import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutationAtSmallPlace
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem permSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j P W _ _ w _ _ _ => permAt p j P w⟩⟩⟩
end GlobalTheory.FramePerm
end
end
