import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne

open MeasureTheory GlobalTheory.Dec
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.UniTrick

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem continuous_lin {ι : Type} [Fintype ι] (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v))
    (f : V →ₗ[ℂ] EuclideanSpace ℂ ι) (v : V) : Continuous fun g => f (ρ g v) := by
  have h : ∀ i, Continuous fun g => (f (ρ g v)) i := fun i =>
    hρ ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).toLinearMap ∘ₗ f) v
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

variable [MeasurableSpace G] [BorelSpace G]

variable [CompactSpace G]

end GlobalTheory.UniTrick

namespace GlobalTheory

end GlobalTheory
