import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetIsotropic

section BC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
  {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem ext_of_isBC {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ} (hm : m.IsBC) {d₁ d₂ : Crys κ' t' A'}
    (h : ∀ c, d₁ (m.pull c) = d₂ (m.pull c)) : d₁ = d₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

end BC

end GlobalTheory.JetIsotropic
