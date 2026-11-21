import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.TorsionRepresent

section
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ)

noncomputable def incl : GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k ⟶ G :=
  pullback.fst ((𝟙 G : G ⟶ G) ^ k) η[G]

instance : Mono (incl G k) := by
  have : Mono η[G] := ⟨fun _ _ _ => toUnit_unique _ _⟩
  exact pullback.fst_of_mono

end

end GlobalTheory.TorsionRepresent
