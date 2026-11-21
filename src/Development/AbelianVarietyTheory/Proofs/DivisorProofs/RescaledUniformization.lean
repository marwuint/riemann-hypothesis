import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HolUnifScale

variable {g : ℕ}

def scaleLin (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) where
  toFun w := fun j ↦ lam j * w j
  invFun w := fun j ↦ (lam j)⁻¹ * w j
  map_add' a b := by funext j; simp [mul_add]
  map_smul' c a := by funext j; simp; ring
  left_inv w := by funext j; exact inv_mul_cancel_left₀ (h j) _
  right_inv w := by funext j; exact mul_inv_cancel_left₀ (h j) _

def scale (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (scaleLin lam h).toContinuousLinearEquiv

@[simp] lemma scale_apply (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) (w : Fin g → ℂ) :
    scale lam h w = fun j ↦ lam j * w j := rfl

variable {A : Over (Sp ℂ)} [GrpObj A] {Lb : LB A.left}

def latPull (u : HolUnif A Lb g) (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) : Submodule ℤ (Fin g → ℂ) :=
  ZLattice.comap ℝ u.Λ ((scaleLin lam h).restrictScalars ℝ).toLinearMap

lemma mem_latPull (u : HolUnif A Lb g) (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) (z : Fin g → ℂ) :
    z ∈ latPull u lam h ↔ scale lam h z ∈ u.Λ := Iff.rfl

end GlobalTheory.HolUnifScale

namespace GlobalTheory.HolUnifScale

end GlobalTheory.HolUnifScale

