import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatTors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Generic

variable {R : Type} [CommRing R] [IsDomain R]

def OverGen (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Over (Sp R)) (x : Sp F ⟶ T.left) : Prop :=
  x ≫ T.hom = jFK (R := R) F ≫ jK R

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

def IsImage (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (q : QkPt P.D.toPre F k)
    (v : Sp F ⟶ t.G.left) : Prop :=
  ∃ a : TFK (R := R) F ⟶ P.A.A, a.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = v ∧ P.ToA F k q a

end GlobalTheory.FlatTors
