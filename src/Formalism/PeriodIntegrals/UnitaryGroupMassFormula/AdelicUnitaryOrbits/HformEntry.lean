import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice

noncomputable section

namespace PIW.AdelicOrbitU

open Matrix Formalism.UG

section Refl

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem hform_eq_dot (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_left (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by
  simp only [hform_eq_dot, dotProduct, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y z : Fin n → S) :
    hform s J x (y - z) = hform s J x y - hform s J x z := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_left (a : S) (x y : Fin n → S) :
    hform s J (a • x) y = s a * hform s J x y := by
  simp only [hform_eq_dot, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem hform_conj (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by
  have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
    have h1 := congrFun (congrFun hJ j) i
    unfold cT at h1
    simpa [Matrix.transpose_apply, Matrix.map_apply] using h1
  unfold hform
  simp only [map_sum, map_mul, hs, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Refl

end PIW.AdelicOrbitU
