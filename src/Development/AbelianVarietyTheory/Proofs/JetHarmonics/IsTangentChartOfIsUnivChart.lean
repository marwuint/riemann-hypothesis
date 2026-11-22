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

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

variable {V : Type} [CommRing V] [IsDomain V]

variable {t : SAB H (Spec (CommRingCat.of V))} {t' : SAB H (Spec (CommRingCat.of (FractionRing V)))}

end Rank

end GlobalTheory.LieLatCompare
