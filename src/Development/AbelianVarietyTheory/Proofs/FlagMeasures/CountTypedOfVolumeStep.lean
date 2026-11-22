import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundled
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat

open Formalism.MainNotions.PlaceDegreeData

namespace GlobalTheory.CountBridge

theorem count_typed_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀,
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.PlaceDegreeData.PointsLemma D n₁ A C (1 / 16) (1 / 16) := by
  intro hV A
  obtain ⟨n₀, C₀, hC₀, hcount⟩ := _root_.GlobalTheory.CountBridge.count_unbundled (_root_.GlobalTheory.CountFinal.countingTheorem_of_volumeStep hV) A
  refine ⟨n₀, C₀, hC₀, fun n₁ hn₁ C hC _D => ?_⟩
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h hSet hData
  exact hcount n₁ hn₁ C hC I b lam g g₀ e H σ w Hs σs tens μf fund R Re h hSet hData

end GlobalTheory.CountBridge
