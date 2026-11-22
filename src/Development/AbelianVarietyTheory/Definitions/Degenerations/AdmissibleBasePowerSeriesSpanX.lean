import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.PelModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
  (I : Ideal R)

def zeroTriple : SAB H (Sp R) :=
  { GlobalTheory.Models.Inhab.zeroTriple H (Sp R) with
    PP := (UnifZero.zeroPre R I).LG
    cub := (UnifZero.zeroPre R I).cubG
    sym := PrimNorm.isSymmetric_of_hasGen _ ⟨UU.unitGen _ _, UU.unitGen_isGen _ _⟩
    adj := (GlobalTheory.Models.Inhab.zeroTriple H (Sp R)).adj
    prim := (GlobalTheory.Models.Inhab.zeroTriple H (Sp R)).prim }

end GlobalTheory.LN.PelModel
end
