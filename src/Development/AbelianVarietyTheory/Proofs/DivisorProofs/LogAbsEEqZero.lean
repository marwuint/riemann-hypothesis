import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.CtTyp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_pos (t : (AE F E)ˣ) : 0 < (absE F E t : ℝ) := by
  have h : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : absE F E t ≠ 0 := left_ne_zero_of_mul_eq_one h
  exact_mod_cast pos_iff_ne_zero.2 h0

def twAbs (χ : Chr F E) (s : ℝ) : (AE F E)ˣ →* ℂˣ where
  toFun t := Units.mk0 ((χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (absE_pos t) s).ne'))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Units.val_mul, Units.val_mk0]
    rw [Real.mul_rpow (absE_pos x).le (absE_pos y).le]
    push_cast
    ring

@[simp] theorem coe_twAbs (χ : Chr F E) (s : ℝ) (t : (AE F E)ˣ) :
    ((twAbs χ s t : ℂˣ) : ℂ) = (χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ) := rfl

end GlobalTheory.CtTyp
