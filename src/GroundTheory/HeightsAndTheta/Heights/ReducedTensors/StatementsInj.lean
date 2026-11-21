import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ReducedTensors
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField TensorProduct
  GroundTheory.Arith.SchemeCoh ComplexAt

universe u

noncomputable section

namespace ProjScheme

end ProjScheme

namespace SectionsLattice

end SectionsLattice

namespace ProjScheme

theorem complexAt_smul_eq_zero {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {a : 𝓞 K}
    (ha : a ≠ 0) {z : ComplexAt σ} (h : a • z = 0) : z = 0 := by
  rw [ComplexAt.smul_def] at h
  have h' := congrArg (ofComplex σ).symm h
  rw [map_mul, AlgEquiv.symm_apply_apply, map_zero, mul_eq_zero] at h'
  rcases h' with h' | h'
  · exact absurd h' ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha))
  · exact (ofComplex σ).symm.injective (h'.trans (map_zero _).symm)

theorem linearIndependent_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) :
    LinearIndependent (𝓞 K) (fun _ : Unit ↦ (1 : ComplexAt σ)) :=
  LinearIndependent.of_subsingleton' () fun r hr ↦ by
    by_contra h
    have h1 := congrArg (ofComplex σ).symm (complexAt_smul_eq_zero h hr)
    rw [map_one, map_zero] at h1
    exact one_ne_zero h1

end ProjScheme

end

end GroundTheory.Heights₂.Heights
