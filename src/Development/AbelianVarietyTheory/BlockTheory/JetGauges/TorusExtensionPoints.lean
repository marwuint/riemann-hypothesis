import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusExtensionPoints

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Defs

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev cT (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

abbrev zeroT (T : Over (Spec (CommRingCat.of R))) : T ⟶ D.P.A := toUnit T ≫ η[D.P.A]

def lamInvφ {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cT D T χ) b).left, (cT D T χ).left, b.left, (zeroT D T).left]

def cubT {T : Over (Spec (CommRingCat.of R))} (x x' y : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left

structure GtPt (T : Over (Spec (CommRingCat.of R))) where
  b : T ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (lamInvφ D b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (cubT D (cT D T χ) (cT D T χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))

namespace GtPt

variable {D} {T : Over (Spec (CommRingCat.of R))}

def IsZero (g : GtPt D T) : Prop :=
  g.b = zeroT D T ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)

def IsAdd (g g' g'' : GtPt D T) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (cubT D (cT D T χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))

def IsNsmul (k : ℕ) (g h : GtPt D T) : Prop :=
  ∃ gs : Fin (k + 1) → GtPt D T, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h

end GtPt

variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.TorusExtensionPoints
