import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsCyclicClassPolynomial

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKP

structure Raw (K R : Type) [Field K] [Ring R] [Algebra ℚ R] where

  A : AbVar K

  ia : R →ₐ[ℚ] End0 A

  L : LB A.X.left
  hL : L.IsLB

section General

variable {K R : Type} [Field K] [Ring R] [Algebra ℚ R]

def Raw.c (X : Raw K R) : Pic X.A.X.left := cls X.L X.hL

end General

section CM

variable {M : Type} [Field M] [NumberField M]

variable [IsCMField M]

def cj (x : M) : M := IsCMField.complexConj M x

def TotPos (h : M) : Prop := cj h = h ∧ ∀ φ : M →+* ℂ, 0 < (φ h).re

def sigH {d : ℕ} (H : Fin d → M) (x : Matrix (Fin d) (Fin d) M) : Matrix (Fin d) (Fin d) M :=
  Matrix.of fun i j => (H i)⁻¹ * cj (x j i) * H j

end CM

end GlobalTheory.LKP
