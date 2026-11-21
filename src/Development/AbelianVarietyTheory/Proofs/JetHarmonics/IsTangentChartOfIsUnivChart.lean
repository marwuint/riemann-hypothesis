import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.EigenLatticeRankLie

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace GlobalTheory.LieLatCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (OAct Host Datum SAB SABMap DetCond LieMult IsLieEigen epsPt epsScale Sp)

attribute [local instance] Over.cartesianMonoidalCategory

section Rank

def under {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (y : Over.mk a ⟶ G) : X ⟶ G.left := y.left

theorem under_comp {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (y : Over.mk a ⟶ G) (f : G ⟶ G) :
    under (y ≫ f) = under y ≫ f.left := rfl

theorem isLieEigen_under {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [Field k] {O : Type} [CommRing O]
    (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen act t τ v ↔
      Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ under v = under (1 : Over.mk t ⟶ G) ∧
        ∀ a, under v ≫ (act.act a).left = Geo.Tor.spMap (epsScale (τ a)) ≫ under v := Iff.rfl

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}

theorem under_scale {k : Type} [Field k] [Algebra R k] (d : k) (w : sp (R₀ := R) (DualNumber k) ⟶ G) :
    under (spMap (scaleOver R d) ≫ w) = Geo.Tor.spMap (epsScale d) ≫ under w := rfl

theorem under_fst {k : Type} [Field k] [Algebra R k] (w : sp (R₀ := R) (DualNumber k) ⟶ G) :
    under (spMap (fstOver R k) ≫ w) = Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ under w := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

variable {V : Type} [CommRing V] [IsDomain V]

variable {t : SAB H (Spec (CommRingCat.of V))} {t' : SAB H (Spec (CommRingCat.of (FractionRing V)))}

end Rank

end GlobalTheory.LieLatCompare
