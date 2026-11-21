import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

section Lie

variable {R : Type} [CommRing R]

def lieAdd (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (x y : LieG G) : LieG G :=
  ⟨x.1 * y.1, by
    rw [MonObj.comp_mul, x.2, y.2]
    exact mul_one (1 : specO R R ⟶ G)⟩

def lieMap {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    (x : LieG T) : LieG G :=
  ⟨x.1 ≫ u, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩

def LieCongr (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (I : Ideal R) (x y : LieG G) : Prop :=
  ∃ a ∈ I, ∃ z : LieG G, x = lieAdd G y (lieScale G a z)

def IsLieLinear {G H : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj H]
    (f : LieG G → LieG H) : Prop :=
  (∀ x y, f (lieAdd G x y) = lieAdd H (f x) (f y)) ∧
    ∀ (a : R) (x : LieG G), f (lieScale G a x) = lieScale H a (f x)

abbrev torus (R : Type) [CommRing R] (r : ℕ) : Over (Spec (CommRingCat.of R)) :=
  splitTorus (Spec (CommRingCat.of R)) (Fin r → ℤ)

def lieCoord {r : ℕ} (x : LieG (torus R r)) (i : Fin r) : R :=
  TrivSqZeroExt.snd (R := R) (M := R)
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom
      (x.1.left.appTop.hom (charUnit (Spec (CommRingCat.of R)) (Fin r → ℤ) (Pi.single i 1)).val))

end Lie

abbrev baseChange (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) ⥤ Over (Spec (CommRingCat.of A)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))

end GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps
