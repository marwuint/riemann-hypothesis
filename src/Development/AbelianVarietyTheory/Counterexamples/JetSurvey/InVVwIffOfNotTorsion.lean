import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PowEqOneOfLocalLift
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FunEqZeroOfAffine

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.WeightProbe
variable {S : Scheme.{0}}

theorem exists_symLift_top (P : PolAV S) {N : ℕ} (hN : Odd N) {T : Over S} (x : T ⟶ P.A) (hx : x ^ N = 1) :
    ∃ U : ThetaGrp P.A P.L N T, SymLift P.A P.L N N x U := by
  have g := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have lft := (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube
    GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2
  have neg := GlobalTheory.exists_gen_negLB g
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local g P.isAb P.isLB hN
    ((GlobalTheory.symLift_odd g lft neg).1 S P N hN T x hx).1
  obtain ⟨nu, hnu⟩ := neg S P N T
  exact SymLiftOdd.exists_symLift g P.isAb P.isLB hN hx θ hθ hnu

open GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank VVCompare CommPairing in

theorem act_pull (P : PolAV S) {N : ℕ} (hN : Odd N) {T T' : Over S} (u : T' ⟶ T) {x : T ⟶ P.A}
    {θ : ThetaGrp P.A P.L N T} {θ' : ThetaGrp P.A P.L N T'} (H : SymLift P.A P.L N N x θ)
    (H' : SymLift P.A P.L N N (u ≫ x) θ') {s t : LB.Sec (LPow P.A P.L N T)} (a : IsActOf P.A P.L N θ s t) :
    IsActOf P.A P.L N θ' (pullS P.A N u s) (pullS P.A N u t) := by
  obtain ⟨ξ, Hξ, v⟩ := SymLiftGlobal.exists_symLift_pull_val P.isLB u H
  have c := SymLiftOdd.symLift_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns P.isAb P.isLB hN θ' ξ H' Hξ
  refine VVCompare.isTwistPull_of_sv P.A P.isLB θ'.isGen fun y J hJ => ?_
  have e : tval θ' (𝟙 _) y J = tval θ (𝟙 _ ≫ (u ▷ P.A).left) y J := (val_corr hJ c _).trans (v _ _ y J hJ)
  have e' : (𝟙 _ ≫ (translT P.A θ'.pt).left) ≫ (u ▷ P.A).left =
      (𝟙 _ ≫ (u ▷ P.A).left) ≫ (translT P.A θ.pt).left := by
    rw [H'.pt_eq, H.pt_eq, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  rw [VVCompare.sv_pullS P.A _ u t _ y hJ, VVCompare.sv_pullS P.A _ u s _ y hJ, e']
  exact (VVCompare.sv_of_isTwistPull P.A a _ y hJ).trans (congrArg (fun q => Units.val q * _) e.symm)

end GlobalTheory.WeightProbe
