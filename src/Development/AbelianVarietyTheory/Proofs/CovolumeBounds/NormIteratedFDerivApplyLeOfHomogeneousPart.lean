import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Metric Set
open scoped Nat ContDiff

namespace GlobalTheory.SCV

section Homogeneous

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def homogeneousPart (c : ℕ) (F : E → V) (a : E) (v : E) : V :=
  (c ! : ℂ)⁻¹ • iteratedFDeriv ℂ c F a (fun _ => v)

@[simp] theorem homogeneousPart_zero (F : E → V) (a v : E) : homogeneousPart 0 F a v = F a := by
  simp [homogeneousPart]

variable [FiniteDimensional ℂ E] [CompleteSpace V]

end Homogeneous

end GlobalTheory.SCV
