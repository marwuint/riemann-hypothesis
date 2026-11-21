import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsogParam

def zpW (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

structure Pt (p : ℕ) {k : Type} [Field k] {O : Type} [Ring O] (star : O ≃+* Oᵐᵒᵖ) (A₀ : AbVar k)
    (ι₀ : O →+* End A₀) (c₀ : Pic A₀.X.left) where

  A : AbVar k

  act : O →+* End A

  c : Pic A.X.left
  ample : IsAmpleCls c
  rosati : ∀ b : O, IsAdj (A := A) (B := A) c c (act b) 1 (act (star b).unop)
  primeToP : ∃ e : ℕ, e.Coprime p ∧ ∀ (Y : Over (Sp k)) (x : Y ⟶ A.X),
    AbVar.lam c (fst Y A.X ≫ x) (snd Y A.X) = 0 → x ^ e = 1

  f : A₀ ⟶ A

  N : ℕ
  N_pos : 0 < N
  isog : IsIsogeny f
  lin : ∀ b : O, ι₀ b ≫ f = f ≫ act b

  den : ℕ

  num : ℕ
  den_pos : 0 < den
  num_pos : 0 < num
  pol : den • AbVar.lam c (fst A₀.X A₀.X ≫ f.hom) (snd A₀.X A₀.X ≫ f.hom) = num • AbVar.lam c₀ (fst A₀.X A₀.X) (snd A₀.X A₀.X)

end GlobalTheory.IsogParam
