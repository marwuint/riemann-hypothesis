import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

abbrev L : Type := FractionRing (MvPolynomial (Fin 2) ℚ)

def xL (i : Fin 2) : L := algebraMap (MvPolynomial (Fin 2) ℚ) L (X i)

theorem xL_ne_zero (i : Fin 2) : xL i ≠ 0 := by
  unfold xL
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact X_ne_zero i

def u : L := xL 1 / xL 0

abbrev Ω : Type := ↥(IntermediateField.adjoin ℚ ({u} : Set L))

def gen : Ω := IntermediateField.AdjoinSimple.gen ℚ u

theorem coe_gen : (gen : L) = u := rfl

theorem gen_ne_zero : gen ≠ 0 := by
  intro h
  have : (gen : L) = 0 := by rw [h]; rfl
  rw [coe_gen, u] at this
  exact div_ne_zero (xL_ne_zero 1) (xL_ne_zero 0) this

def yLine : (Σ _ : Unit, Fin 2) → Ω := fun p => if p.2 = 0 then 1 else gen

theorem yLine_ne_zero (p : Σ _ : Unit, Fin 2) : yLine p ≠ 0 := by
  unfold yLine
  split_ifs
  · exact one_ne_zero
  · exact gen_ne_zero

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
