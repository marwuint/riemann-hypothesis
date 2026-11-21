import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatTest

open Module NumberField TensorProduct

section Eigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl

theorem expand_dual (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm

theorem repr_eq_trace (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
    ← integralBasis_apply, trace_dualInt]
  simp

end Eigen

end GlobalTheory.CompanionTheory.Ar.HT.LatTest
