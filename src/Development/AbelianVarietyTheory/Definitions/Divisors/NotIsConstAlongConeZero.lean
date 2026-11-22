import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out.InhTate
open GlobalTheory.Toroidal GlobalTheory.ToricData

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart.Model

theorem constHom_apply {R k : Type} [CommRing R] [Field k] (ρ : R →+* DualNumber k) (r : R) :
    constHom ρ r = TrivSqZeroExt.inl (ρ r).fst := rfl

variable {R : Type} [CommRing R] [IsDomain R] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (q : X → (FractionRing R)ˣ) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ X)

abbrev A : Type := PowerSeries (PowerSeries ℚ)

abbrev tt : A := PowerSeries.X

abbrev ss : A := PowerSeries.C PowerSeries.X

def frm : LinearMap.BilinForm ℤ (ℤ × ℤ) := LinearMap.mk₂ ℤ (fun y z => 2 * (y.1 * z.1 + y.2 * z.2))
  (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

def nrm (y : ℤ × ℤ) : ℕ := (y.1 * y.1 + y.2 * y.2).toNat

def per (v : Aˣ) (b : ℤ × ℤ → ℤ) (y : ℤ × ℤ) : (FractionRing A)ˣ :=
  Units.mk0 (algebraMap A _ (tt ^ nrm y * (v ^ b y : Aˣ)))
    ((map_ne_zero_iff _ (IsFractionRing.injective A _)).2
      (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (Units.ne_zero _)))

end GlobalTheory.RigChart.Model
