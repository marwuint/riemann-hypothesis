import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.GrowthW

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def hsN {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))

theorem hsN_nonneg {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hsN g :=
  Real.sqrt_nonneg _

def SUpper {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Prop := ∀ i j : Fin m, j ≤ i → X i j = 0

def LieNUpper : Prop := ∀ (k r : ℕ) (X : Formalism.FourierDecayAlt.B.Mat k r), PI.WUN.InLieN k r X → SUpper X

def ExpUpper : Prop :=
  ∀ m : ℕ, 0 < m → ∃ C D : ℝ, 0 < D ∧ ∀ X : Matrix (Fin m) (Fin m) ℂ, SUpper X →
    1 + hsN X ≤ C * hsN (NormedSpace.exp X) ^ D

section Assembly

variable {k r : ℕ}

theorem norm_le_hsN (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    ‖x‖ ≤ hsN (unrealify x) := by
  rw [EuclideanSpace.norm_eq]
  unfold hsN
  apply le_of_eq
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [unrealify, Complex.normSq_mk, Real.norm_eq_abs, sq_abs]
  ring

end Assembly

end Formalism.MainNotions.GrowthW
