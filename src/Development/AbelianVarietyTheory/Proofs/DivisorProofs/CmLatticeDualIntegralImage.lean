import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CxDescent

noncomputable def imForm (n : ℕ) (ρ : ℝ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v u => (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im)
    (by intro v v' u; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))
    (by intro v u u'; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))

theorem imForm_apply (n : ℕ) (ρ : ℝ) (v u : Fin n → ℂ) :
    imForm n ρ v u = (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im := rfl

end GlobalTheory.CxDescent
