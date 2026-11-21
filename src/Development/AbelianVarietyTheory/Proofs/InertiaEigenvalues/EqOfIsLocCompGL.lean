import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwasawaDecompositionSmoothNearOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalSum

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped ContDiff

namespace GlobalTheory.DiscSMO

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a c N : ℕ} {n : Fin c → ℕ}
  {π π' : ∀ i, CuspSub E (n i)}

namespace IsTensorOf

end IsTensorOf

variable {h : ∑ i, n i = N}

namespace IsTensorOf

end IsTensorOf

theorem mem_Sm_of_one {f : GA E a → ℂ} (hf : ∀ g, ContDiffAt ℝ ∞ (chart f g) (oneL E a)) : f ∈ Sm E a := by
  rintro g x ⟨y, hy⟩
  obtain rfl : x = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  rw [e]
  refine (ContDiffAt.comp _ ?_ (lmul (toL (y⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt
  rw [e1]
  exact hf _

theorem contDiffAt_chart_mul {f : GA E a → ℂ} {g : GA E a} {y : GL (Fin a) (Cinf E)}
    (hf : ContDiffAt ℝ ∞ (chart (fun x => f (x * infGL E a y)) g) (oneL E a)) :
    ContDiffAt ℝ ∞ (chart f (g * infGL E a y)) (oneL E a) := by
  have e : chart f g = chart (fun x => f (x * infGL E a y)) g ∘ rmul (toL (y⁻¹).val) := by
    rw [← chart_rt_inf]
    simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have e1 : rmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.mul_inv
  have e2 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  rw [chart_mul, e]
  refine ContDiffAt.comp _ ?_ (lmul (toL y.val)).contDiff.contDiffAt
  rw [e2]
  refine ContDiffAt.comp _ ?_ (rmul (toL (y⁻¹).val)).contDiff.contDiffAt
  rw [e1]
  exact hf

namespace IsTensorOf

end IsTensorOf

end GlobalTheory.DiscSMO

end
