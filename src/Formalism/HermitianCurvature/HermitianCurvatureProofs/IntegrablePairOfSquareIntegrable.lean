import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFderivChiBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section L2

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem norm_hs_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsInner A A‖ + ‖B.hsInner C C‖ := by
  unfold B.hsInner
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (B.hsVec C) (B.hsVec A)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm]
  nlinarith [norm_nonneg (B.hsVec A), norm_nonneg (B.hsVec C), sq_nonneg (‖B.hsVec A‖ - ‖B.hsVec C‖)]

end L2

end Formalism.FourierDecayAlt.P5.HerB
