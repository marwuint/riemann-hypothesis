import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.HasCoverByOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def colRestrict {s : ℕ} (A : Fin s → Fin 2) : (Fin 2 → Ω) →ₗ[Ω] (Fin s → Ω) where
  toFun w a := w (A a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordFun (s : ℕ) (m : Fin 2) : Module.Dual Ω (⋀[Ω]^s (Fin 2 → Ω)) :=
  exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating (n := Fin s) (R := Ω)).compLinearMap (colRestrict fun _ => m))

def pick (A : Fin 1 → Fin 2) (m : Fin 2) : Ω := if m = A 0 then 1 else 0

theorem pick_mem (c : Unit → Fin 2) (A : Fin 1 → Fin 2) (m : Fin 2) :
    (1 : Ω) ^ 0 * pick A m ∈ chartRing ℤ (segreCoord yLine) c := by
  unfold pick
  split_ifs
  · simp
  · simp

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
