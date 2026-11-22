import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.TopAmpSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.FamInh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Model

theorem isProjOver_powObj {R : Type} [CommRing R] (A : Over (Sp R)) (h : IsProjOver A.hom) :
    ∀ n, IsProjOver (Out.powObj A n).hom
  | 0 => Inhab.isProjOver_id R
  | n + 1 => ProjSpace.isProjOver_pullback h (isProjOver_powObj A h n)

end Model

end GlobalTheory.Models.FamInh

end
