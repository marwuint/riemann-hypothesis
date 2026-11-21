import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

variable (d : IndexData)

def shLin (τ : Fin d.f) : XPoly d →ₗ[ℚ] ℚ where
  toFun := shiftFl d τ
  map_add' F G := by simp [shiftFl, Finset.sum_add_distrib]
  map_smul' c F := by simp [shiftFl, ← Finset.smul_sum]

def totLin (τ : Fin d.f) : XPoly d →ₗ[ℚ] ℚ where
  toFun := totalFl d τ
  map_add' F G := by simp [totalFl, Finset.sum_add_distrib]
  map_smul' c F := by simp [totalFl, ← Finset.smul_sum]

abbrev topSpace : Submodule ℚ (XPoly d) := homogeneousSubmodule (Idx d) ℚ (d.D + 1)

def shOn (τ : Fin d.f) : topSpace d →ₗ[ℚ] ℚ := (shLin d τ).comp (topSpace d).subtype

def totOn (τ : Fin d.f) : topSpace d →ₗ[ℚ] ℚ := (totLin d τ).comp (topSpace d).subtype

variable {d}

end GroundTheory.Heights₂.Heights.TheoremB
