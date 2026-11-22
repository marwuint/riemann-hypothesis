import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Inhab

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem val_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) =
      pullRatio (prB n k) W i (h.trans ((prB n k).preimage_mono inf_le_left)) j := by
  rw [← appLE_ratioOn (φ := prB n k) (W := W) (U := chart ℤ (n k) i ⊓ chart ℤ (n k) j)
    (i := i) (j := j) inf_le_left h]
  rfl

theorem blockUnit_mul {k : Fin (m + 1)} (i j l : Bk n k) {W : (MP ℤ m n).Opens}
    (h₁ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (h₂ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) j ⊓ chart ℤ (n k) l))
    (h₃ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) l)) :
    blockUnit i j h₁ * blockUnit j l h₂ = blockUnit i l h₃ := by
  refine Units.ext ?_
  rw [Units.val_mul, val_blockUnit, val_blockUnit, val_blockUnit]
  exact pullRatio_mul_pullRatio

theorem prod_blockUnit_single {W : (MP ℤ m n).Opens} (k : Fin (m + 1)) (c c' : ∀ k, Bk n k)
    (h : ∀ k', W ≤ prB n k' ⁻¹ᵁ (chart ℤ (n k') (c k') ⊓ chart ℤ (n k') (c' k'))) :
    (∏ k', blockUnit (c k') (c' k') (h k') ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') =
      blockUnit (c k) (c' k) (h k) := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

end GlobalTheory.CompanionTheory.MPDict.Inhab

