import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Model

def vecFunctor (X : Scheme.{0}) (d : ℕ) : (Over X)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Multiplicative (Fin d → Γ(T.unop.left, ⊤)))
  map g := GrpCat.ofHom (MonoidHom.mk' (fun v => Multiplicative.ofAdd fun j => g.unop.left.appTop.hom (v.toAdd j))
    fun v w => funext fun j => map_add g.unop.left.appTop.hom (v.toAdd j) (w.toAdd j))
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun v => funext fun j =>
    congrArg (fun q => q.hom (v.toAdd j)) (Scheme.Hom.id_appTop (X := T.unop.left)))
  map_comp g g' := GrpCat.hom_ext (MonoidHom.ext fun x => rfl)

def vecObj (X : Scheme.{0}) (d : ℕ) : Over X := Over.mk (𝔸(Fin d; X) ↘ X)

def vecEquiv {X : Scheme.{0}} {d : ℕ} (T : Over X) :
    (T ⟶ vecObj X d) ≃ Multiplicative (Fin d → Γ(T.left, ⊤)) where
  toFun x := Multiplicative.ofAdd fun j => x.left.appTop (AffineSpace.coord X j)
  invFun v := Over.homMk (AffineSpace.homOfVector T.hom v.toAdd) (AffineSpace.homOfVector_over _ _)
  left_inv x := Over.OverMorphism.ext (AffineSpace.hom_ext
    ((AffineSpace.homOfVector_over _ _).trans (Over.w x).symm) fun i =>
      AffineSpace.homOfVector_appTop_coord _ _ i)
  right_inv v := funext fun j => AffineSpace.homOfVector_appTop_coord _ _ j

def vecRep (X : Scheme.{0}) (d : ℕ) : (vecFunctor X d ⋙ forget _).RepresentableBy (vecObj X d) where
  homEquiv {T} := vecEquiv T
  homEquiv_comp _ _ := rfl

instance (X : Scheme.{0}) (d : ℕ) : GrpObj (vecObj X d) := GrpObj.ofRepresentableBy _ _ (vecRep X d)

theorem vecEquiv_mul {X : Scheme.{0}} {d : ℕ} {T : Over X} (x y : T ⟶ vecObj X d) :
    vecEquiv T (x * y) = vecEquiv T x * vecEquiv T y :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (vecRep X d)).hom.app (Opposite.op T)).hom.map_mul x y

instance (X : Scheme.{0}) (d : ℕ) : IsCommMonObj (vecObj X d) where
  mul_comm := by
    have h : fst (vecObj X d) (vecObj X d) * snd (vecObj X d) (vecObj X d) =
        snd (vecObj X d) (vecObj X d) * fst (vecObj X d) (vecObj X d) :=
      (vecEquiv _).injective (by rw [vecEquiv_mul, vecEquiv_mul, _root_.mul_comm])
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [← lift_snd_fst]
    exact h.symm

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (d : ℕ)

end Model

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
