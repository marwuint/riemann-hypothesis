import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

variable {R : Type} [CommRing R]

def Lifts {X : Scheme.{0}} (s : X ⟶ Sp R) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X) : Prop :=
  z ≫ s = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) ∧
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = P

def unitPt (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] : Sp B ⟶ A.left :=
  spMap (algebraMap R B) ≫ (show Sp R ⟶ A.left from η[A].left)

def IsSum {B M B' M' : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [CommRing B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (α : B → B') (f : M → M') : Prop :=
  (∀ b, β (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (α b)) ∧ ∀ m, β (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (f m)

structure TanRep (A : Over (Sp R)) [GrpObj A] (W : Type) [AddCommGroup W] [Module R W] where

  Φ : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (_ : Sp (TrivSqZeroExt B M) ⟶ A.left), W →ₗ[R] M

  bij : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (l : W →ₗ[R] M),
    ∃! z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z ∧ Φ z = l

  nat : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M']
    [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M'] (α : B →ₐ[R] B') (f : M →ₗ[R] M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f →
    ∀ z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z → Φ (spMap β ≫ z) = f ∘ₗ Φ z

end GlobalTheory.AbTan

namespace GlobalTheory.AbTan.MultGroup

open LaurentPolynomial

variable (R : Type) [CommRing R]

local instance hopfLaurent : HopfAlgebra (CommRingCat.of R) (CommRingCat.of R[T;T⁻¹]) :=
  inferInstanceAs (HopfAlgebra R R[T;T⁻¹])

abbrev G : Over (Sp R) := (Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))

theorem unit_eq (B : Type) [CommRing B] [Algebra R B] :
    unitPt (G R) B = spMap (algebraMap R B) ≫ spMap (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom := rfl

variable {R}

end GlobalTheory.AbTan.MultGroup
