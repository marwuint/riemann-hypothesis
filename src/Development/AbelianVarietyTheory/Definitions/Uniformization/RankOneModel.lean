import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
namespace GlobalTheory.UT.ClModel

theorem galois_all : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Galois U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ F' _ _ _ σ k hk p
  refine ⟨qkExtExists R D.toPre F F' σ.toRingHom (fun r => σ.commutes r) k p, fun x => ?_, fun p' x x' h h' =>
    GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt GlobalTheory.firstFiveLaws R I hI D A G hG U F F' σ k hk p p' x x' h h'⟩
  refine ⟨Over.homMk (spMap σ.toRingHom ≫ x.left) ?_, rfl⟩
  rw [Category.assoc, Over.w x]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  all_goals exact σ.commutes _

end GlobalTheory.UT.ClModel
end
