import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
include hF in
theorem readsCusp_alt : haveI := host_isCMField D.host; ReadsCusp D.naut fun a π => (C.e a π).1 := by
  have := host_isCMField D.host
  refine ⟨fun a _ => Subtype.val_injective.comp (C.e a).injective, fun a π _ => (C.e a π).2, fun a π w _ hu => ?_⟩
  rw [T.frobEig w _ hu, C.loc]
  exact _root_.GlobalTheory.HeightCounting.Blocks.exists_satake_frobenius_eigenvalues_eq_inv_of_unramified hL hF _ _ (by have e := (T.unr w _).1 hu; rwa [C.loc] at e)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
end
end
