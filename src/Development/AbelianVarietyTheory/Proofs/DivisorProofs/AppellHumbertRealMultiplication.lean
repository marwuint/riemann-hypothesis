import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosatiAH

end GlobalTheory.RosatiAH

namespace GlobalTheory.RosatiAH

end GlobalTheory.RosatiAH

namespace GlobalTheory.RosatiAH

variable {g : ℕ}

def dmul (s : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z j := s j * z j
  map_add' z w := by funext j; simp [mul_add]
  map_smul' t z := by funext j; simp; ring

def fdiag (g : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun z := Fin.append z z
  map_add' z w := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply]
  map_smul' t z := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply, RingHom.id_apply]
    · simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]

end GlobalTheory.RosatiAH
