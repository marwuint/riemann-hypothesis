import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.FamTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ}

end GlobalTheory.Models.FamTest

end
