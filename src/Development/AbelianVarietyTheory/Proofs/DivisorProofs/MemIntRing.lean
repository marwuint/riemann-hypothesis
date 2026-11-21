import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV

noncomputable section

open IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.TauNorm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum ℤ)

abbrev Av : Type := v.adicCompletion ℚ ⊗[ℚ] K

abbrev sig (τ : K ≃ₐ[ℚ] K) : Av K v →ₐ[ℚ] Av K v :=
  Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) (τ : K →ₐ[ℚ] K)

variable {K v}

variable (K v)

end GlobalTheory.TauNorm
