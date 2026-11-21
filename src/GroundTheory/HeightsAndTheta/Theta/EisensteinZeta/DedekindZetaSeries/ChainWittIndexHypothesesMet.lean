import Mathlib
import GroundTheory.AutomorphicForms.HermitianSpaces
import GroundTheory.HeightsAndTheta.Theta.CMDatum
import GroundTheory.HeightsAndTheta.Theta.Parabolic
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.HeightsAndTheta.Theta.GaussianExample

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Module NumberField GroundTheory.Automorphic

universe u

instance isTotallyComplex_gaussQ : IsTotallyComplex GaussQ where
  isComplex v := by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    intro hv
    set φ := v.embedding
    have hsq : φ (QuadraticAlgebra.omega) * φ (QuadraticAlgebra.omega) = -1 := by
      rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      simp
    have him : (φ (QuadraticAlgebra.omega)).im = 0 := by
      have := RingHom.congr_fun hv (QuadraticAlgebra.omega)
      rw [ComplexEmbedding.conjugate_coe_eq] at this
      exact Complex.conj_eq_iff_im.1 this
    have hre := congrArg Complex.re hsq
    simp only [Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.one_re] at hre
    nlinarith [mul_self_nonneg (φ (QuadraticAlgebra.omega)).re]

end GroundTheory.Heights₂.Theta
