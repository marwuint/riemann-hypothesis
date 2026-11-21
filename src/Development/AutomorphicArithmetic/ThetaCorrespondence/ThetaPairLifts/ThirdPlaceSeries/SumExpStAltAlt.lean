import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatement
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SumExpAt
end GlobalTheory.SumExpAt
namespace GlobalTheory.SumExpAt
end GlobalTheory.SumExpAt
namespace GlobalTheory.ExpTie
open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
theorem sumExpSt_alt : _root_.GlobalTheory.ExpTie.ExponentSumStatement :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun _ _ _ p _ _ j P W hD _ t w => lIncl_sumExp p j P W hD t w⟩⟩
end GlobalTheory.ExpTie
end
end
