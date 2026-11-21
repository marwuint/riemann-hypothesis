import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpTorsionDefOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def sharpPair (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (a b : Fin 8) : D.P.A.left ⟶ (G2 Q.B).left :=
  (lift (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr a))
    (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr b))).left

end GlobalTheory.Poinc.Sep
