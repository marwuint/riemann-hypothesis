import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def BlowAt (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (φ : InvFun ℤ) (d : ℕ)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S) : Prop :=
  ∃ J : Z.IdealSheafData, 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧
    IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
    BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d

end GlobalTheory.SiegJoin
