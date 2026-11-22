import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem weilIs_baseChange_of_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] [IsCommMonObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (_ : IsGrpPullback G' G f φ) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S') (n : ℤ) (x' y' : Over.mk t ⟶ G') (x y : Over.mk (t ≫ f) ⟶ G) (c : Rˣ), x.left = x'.left ≫ φ → y.left = y'.left ≫ φ → (Out.WeilIs G' L' n x' y' (unitOn c) ↔ Out.WeilIs G L n x y (unitOn c)) :=
  fun S S' G G' _ _ _ f φ h L L' hL hL' hw _ _ t n x' y' x y c ex ey =>
    weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' h hw (Over.mk t) n x' y' x y (unitOn c) ex ey

namespace WeilNoncomm

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

@[ext] structure Heis (R : Type) where

  a : R

  b : R

  c : R

namespace Heis

variable {R R' : Type} [CommRing R] [CommRing R']

instance : Mul (Heis R) := ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩⟩
instance : One (Heis R) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Heis R) := ⟨fun g => ⟨-g.a, -g.b, -g.c + g.a * g.b⟩⟩

theorem mul_def (g h : Heis R) : g * h = ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩ := rfl
theorem one_def : (1 : Heis R) = ⟨0, 0, 0⟩ := rfl
theorem inv_def (g : Heis R) : g⁻¹ = ⟨-g.a, -g.b, -g.c + g.a * g.b⟩ := rfl

instance : Group (Heis R) := Group.ofLeftAxioms
  (fun g h k => by ext <;> simp only [mul_def] <;> ring)
  (fun g => by ext <;> simp [mul_def, one_def])
  (fun g => by ext <;> simp [mul_def, one_def, inv_def])

def map (f : R →+* R') : Heis R →* Heis R' :=
  MonoidHom.mk' (fun g => ⟨f g.a, f g.b, f g.c⟩) fun g h => by ext <;> simp [mul_def]

end Heis

def heisFunctor (S : Scheme.{0}) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Heis Γ(T.unop.left, ⊤))
  map f := GrpCat.ofHom (Heis.map f.unop.left.appTop.hom)
  map_id T := by
    ext g <;> simp [Heis.map]
  map_comp f g := rfl

abbrev heisScheme (S : Scheme.{0}) : Over S := Over.mk (𝔸(Fin 3; S) ↘ S)

def heisRepr (S : Scheme.{0}) : (heisFunctor S ⋙ forget _).RepresentableBy (heisScheme S) where
  homEquiv {T} :=
    { toFun := fun f => (⟨f.left.appTop (AffineSpace.coord S 0), f.left.appTop (AffineSpace.coord S 1),
        f.left.appTop (AffineSpace.coord S 2)⟩ : Heis Γ(T.left, ⊤))
      invFun := fun g : Heis Γ(T.left, ⊤) => Over.homMk (AffineSpace.homOfVector T.hom ![g.a, g.b, g.c])
        (AffineSpace.homOfVector_over _ _)
      left_inv := fun f => Over.OverMorphism.ext (AffineSpace.hom_ext
        ((AffineSpace.homOfVector_over _ _).trans (Over.w f).symm) fun i =>
          (AffineSpace.homOfVector_appTop_coord _ _ i).trans (by fin_cases i <;> rfl))
      right_inv := fun g => Heis.ext (AffineSpace.homOfVector_appTop_coord _ _ 0)
        (AffineSpace.homOfVector_appTop_coord _ _ 1) (AffineSpace.homOfVector_appTop_coord _ _ 2) }
  homEquiv_comp f g := rfl

@[reducible] def heisGrp (S : Scheme.{0}) : GrpObj (heisScheme S) := GrpObj.ofRepresentableBy _ _ (heisRepr S)

attribute [local instance] heisGrp

def heisPt {S : Scheme.{0}} (T : Over S) : (T ⟶ heisScheme S) →* Heis Γ(T.left, ⊤) :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (heisRepr S)).hom.app (Opposite.op T)).hom

end WeilNoncomm

end GlobalTheory
