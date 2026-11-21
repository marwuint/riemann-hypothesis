import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqExpFderiv

open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate

namespace GlobalTheory.Doubling

noncomputable section

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_cexp_fderiv_of_map_add {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by
  first
  | exact @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | (apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv ..)

end Character

end

end GlobalTheory.Doubling
