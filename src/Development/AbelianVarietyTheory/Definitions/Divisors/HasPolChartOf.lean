import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Act

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

structure Data.Act (O : Type) [Ring O] [StarRing O] (Q : Data R) [Module O Q.X] where

  onB : RingAct Q.B O
  rosati : ∀ a : O, RosatiAdj Q.B Q.M.L (onB.act a) (onB.act (star a))
  c_lin : ∀ (a : O) (y : Q.X), Q.c (a • y) = Q.c y ≫ onB.act a
  tau_bal : ∀ (a : O) (u : LB.Gen (LB.LinComb Q.M.L (rosatiφ Q.B (onB.act a) (onB.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr Q.M.L _ _ _ _ (LB.pullGen Q.M.L _ _ u (zero2 Q.B)) (LB.oneGen Q.M.L) → ∀ y y' z J, Good Q.M.L z J →
      val (Q.tau (a • y) y') (𝟙 _) z J * val u (lift (toUnit (TK R) ≫ Q.c y) (toUnit (TK R) ≫ Q.c y')).left z J =
        val (Q.tau y (star a • y')) (𝟙 _) z J

def HalfAt (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ)
    (β : D.P.A.left ⟶ Q.B.left) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T ⟶ D.P.A) (1 : T ⟶ D.P.A)).left z J J' = 1) ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)) =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

theorem half_iff {Q : Data R} {ρ : R →+* R'} {D : DegPre R'} {e : D.X ≃+ Q.X} {f : D.X → D.X → (FractionRing R')ˣ} :
    Half Q ρ D e f ↔ ∃ β, HalfAt Q ρ D e f β := Iff.rfl

def IsPrim {S : Scheme.{0}} (P : PolAV S) (w : P.A ⟶ P.A) : Prop :=
  letI := P.isAb.comm
  ∃ u : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(padd P.A (𝟙 _) w).left, 𝟙 P.A.left, w.left, (toUnit P.A ≫ η[P.A]).left]
    ![1, -2, -1, 2]), u.IsGen

end Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {o : Type} [CommRing o] {b : o →+* c.F}

end GlobalTheory.PolDeg
