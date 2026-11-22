import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistence
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp.Adapt
end GlobalTheory.BigOn.Exp.Adapt
open GlobalTheory.BigOn.Exp.Adapt in
theorem GlobalTheory.BigOn.Exp.adaptEx_alt : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH _ _ => ⟨0, fun x hx _ i p _ hm w _ j => adapt_at p w j hm⟩⟩⟩
end
end
