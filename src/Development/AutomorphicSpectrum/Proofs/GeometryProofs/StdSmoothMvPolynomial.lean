import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieInh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem stdSmooth_mvPolynomial (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  have hker : (Algebra.Generators.mvPolynomial R (Fin n)).ker = ⊥ := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.mvPolynomial_val]
    exact (RingHom.injective_iff_ker_eq_bot _).1 fun a b h => by
      simpa only [MvPolynomial.aeval_X_left_apply] using h
  let P : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨Algebra.Generators.mvPolynomial R (Fin n), Empty.elim, by rw [hker]; simp⟩
  let P' : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P, Empty.elim, fun a => a.elim⟩
  let P'' : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P', by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
      exact isUnit_one⟩
  refine Algebra.IsStandardSmoothOfRelativeDimension.mk ⟨Fin n, Empty, inferInstance, inferInstance, P'', ?_⟩
  simp [Algebra.Presentation.dimension]

def gaFunctor (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Multiplicative Γ(T.unop.left, ⊤))
  map g := GrpCat.ofHom (MonoidHom.mk' (fun v => Multiplicative.ofAdd (g.unop.left.appTop.hom v.toAdd))
    fun v w => map_add g.unop.left.appTop.hom v.toAdd w.toAdd)
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun v =>
    congrArg (fun q => q.hom v.toAdd) (Scheme.Hom.id_appTop (X := T.unop.left)))
  map_comp g g' := GrpCat.hom_ext (MonoidHom.ext fun x => rfl)

def gaObj (X : Scheme.{0}) : Over X := Over.mk (𝔸(Fin 1; X) ↘ X)

def gaEquiv {X : Scheme.{0}} (T : Over X) :
    (T ⟶ gaObj X) ≃ Multiplicative Γ(T.left, ⊤) where
  toFun x := Multiplicative.ofAdd (x.left.appTop (AffineSpace.coord X 0))
  invFun v := Over.homMk (AffineSpace.homOfVector T.hom fun _ => v.toAdd) (AffineSpace.homOfVector_over _ _)
  left_inv x := Over.OverMorphism.ext (AffineSpace.hom_ext
    ((AffineSpace.homOfVector_over _ _).trans (Over.w x).symm) fun i => by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact AffineSpace.homOfVector_appTop_coord _ _ _)
  right_inv v := AffineSpace.homOfVector_appTop_coord T.hom (fun _ : Fin 1 => v.toAdd) 0

def gaRep (X : Scheme.{0}) : (gaFunctor X ⋙ forget _).RepresentableBy (gaObj X) where
  homEquiv {T} := gaEquiv T
  homEquiv_comp _ _ := rfl

instance (X : Scheme.{0}) : GrpObj (gaObj X) := GrpObj.ofRepresentableBy _ _ (gaRep X)

theorem gaEquiv_mul {X : Scheme.{0}} {T : Over X} (x y : T ⟶ gaObj X) :
    gaEquiv T (x * y) = gaEquiv T x * gaEquiv T y := by
  have hcomp : ∀ {T' : Over X} (f : T ⟶ T') (g : T' ⟶ gaObj X),
      gaEquiv T (f ≫ g) = ((gaFunctor X).map f.op).hom (gaEquiv T' g) := fun _ _ => rfl
  have hμ : gaEquiv (gaObj X ⊗ gaObj X) MonObj.mul =
      gaEquiv _ (fst (gaObj X) (gaObj X)) * gaEquiv _ (snd (gaObj X) (gaObj X)) := by
    erw [MonObj.ofRepresentableBy_mul]
    exact Equiv.apply_symm_apply _ _
  rw [Hom.mul_def, hcomp, hμ, map_mul, ← hcomp, ← hcomp, lift_fst, lift_snd]

instance (X : Scheme.{0}) : IsCommMonObj (gaObj X) where
  mul_comm := by
    have h : fst (gaObj X) (gaObj X) * snd (gaObj X) (gaObj X) =
        snd (gaObj X) (gaObj X) * fst (gaObj X) (gaObj X) :=
      (gaEquiv _).injective (by rw [gaEquiv_mul, gaEquiv_mul, _root_.mul_comm])
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [← lift_snd_fst]
    exact h.symm

variable {X : Scheme.{0}}

variable {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)

end GlobalTheory.CompanionTheory.Ar.LieInh

namespace GlobalTheory.CompanionTheory.Ar

end GlobalTheory.CompanionTheory.Ar
