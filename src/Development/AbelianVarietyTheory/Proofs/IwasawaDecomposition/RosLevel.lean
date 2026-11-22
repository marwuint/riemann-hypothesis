import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAdicColimitOfIsFiniteNoetherian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

abbrev Frame {X Y : Scheme.{0}} (L : LB X) (ψ : Y ⟶ X) : Type :=
  LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1)

section Defs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def Lies {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left),
    y ≫ fGl I G e = r ≫ x' → y ≫ pGl U e = r ≫ b

def FrRel {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) (g' : Frame U.LG.L x')
    (g : Frame D.toPre.P.L b) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left), y ≫ fGl I G e = r ≫ x' →
    ∀ (z : Z) (JM) (JL), Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val g r z JM = wVal U e z JM JL y * val g' r z JL

end Defs

end GlobalTheory.RayEv.Transport
