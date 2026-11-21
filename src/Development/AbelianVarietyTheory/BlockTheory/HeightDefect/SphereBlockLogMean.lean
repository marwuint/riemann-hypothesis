import Mathlib

open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

abbrev UnitSphere (N : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1

def sphereSurface (N : ℕ) : Measure (UnitSphere N) :=
  (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere

def sphereMeasure (N : ℕ) : Measure (UnitSphere N) :=
  (sphereSurface N Set.univ)⁻¹ • sphereSurface N

instance sphereSurface_finite (N : ℕ) : IsFiniteMeasure (sphereSurface N) := by
  unfold sphereSurface; infer_instance

instance sphereSurface_neZero (N : ℕ) : NeZero (sphereSurface N) := by
  refine ⟨fun h => ?_⟩
  have := (Measure.toSphere_eq_zero_iff _).1 h
  exact not_subsingleton _ this

instance sphereMeasure_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (sphereMeasure N) := by
  unfold sphereMeasure; infer_instance

def blockSphereMeasure (B N : ℕ) : Measure (Fin B → UnitSphere N) :=
  Measure.pi fun _ => sphereMeasure N

instance blockSphereMeasure_isProbabilityMeasure (B N : ℕ) :
    IsProbabilityMeasure (blockSphereMeasure B N) := by
  unfold blockSphereMeasure; infer_instance

section NumberField

variable {K : Type} [Field K] [NumberField K]

def gaussAbsValue {ι : Type} (w : FinitePlace K) (ω : MvPolynomial ι K) : ℝ :=
  ((ω.support.sup fun d => Real.toNNReal (w (coeff d ω)) : ℝ≥0) : ℝ)

end NumberField

end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
