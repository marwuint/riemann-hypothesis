import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.FlagCell

def uniR {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun a b => if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem uniR_apply {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) (a b : Fin m) :
    uniR n a b = if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0 := rfl

theorem map_uniR {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (n : Low m → R) :
    (uniR n).map f = uniR fun s => f (n s) := by
  ext a b
  simp only [Matrix.map_apply, uniR_apply]
  split_ifs <;> simp

end GlobalTheory.FlagCell
