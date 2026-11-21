import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] SplitExt.free SplitExt.finite

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev cPt (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

def oφ {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A b (cPt D T χ)).left, (cPt D T χ).left, b.left, (pzero D.P.A T).left]

def oεInv : Fin 4 → ℤ := ![-1, 1, 1, -1]

abbrev oInvLB {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) : LB T.left :=
  LB.LinComb D.P.L (oφ D b χ) oεInv

def cubAt {T : Over (Spec (CommRingCat.of R))} (x x' x'' : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' x'')).left

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

structure GtPt where

  base : TF (R := R) F ⟶ D.P.A

  form : ∀ χ : D.X, LB.Gen (oInvLB D base χ)
  form_gen : ∀ χ : D.X, (form χ).IsGen
  form_mul : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (form (χ + χ')) (cubAt D (cPt D _ χ) (cPt D _ χ') base))
    (LB.mulGen D.P.L _ _ _ _ (form χ) (form χ'))

namespace GtPt

variable {D F}

def IsAdd (g g' h : GtPt D F) : Prop :=
  h.base = padd D.P.A g.base g'.base ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (h.form χ) (cubAt D (cPt D _ χ) g.base g'.base))
      (LB.mulGen D.P.L _ _ _ _ (g.form χ) (g'.form χ))

def IsZero (g : GtPt D F) : Prop :=
  g.base = pzero D.P.A _ ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ) (LB.oneGen D.P.L)

inductive IsNsmul (g : GtPt D F) : ℕ → GtPt D F → Prop
  | zero (h : GtPt D F) : IsZero h → IsNsmul g 0 h
  | succ (k : ℕ) (h h' : GtPt D F) : IsNsmul g k h → IsAdd h g h' → IsNsmul g (k + 1) h'

def IsIo (y : D.X) (g : GtPt D F) : Prop :=
  g.base = cPt D _ y ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ)
      (LB.pullGen D.P.L _ _ (D.io y χ) (jFK (R := R) F))

end GtPt

def QPair (k : ℕ) : Type :=
  {p : D.X × GtPt D F // ∃ h : GtPt D F, p.2.IsNsmul k h ∧ GtPt.IsIo p.1 h}

def QRel (k : ℕ) (p p' : QPair D F k) : Prop :=
  ∃ (z : D.X) (w : GtPt D F), GtPt.IsIo z w ∧ p'.1.1 = p.1.1 + k • z ∧ GtPt.IsAdd p.1.2 w p'.1.2

namespace Qk

end Qk

end GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms
