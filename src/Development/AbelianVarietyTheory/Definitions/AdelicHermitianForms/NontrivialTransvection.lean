import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic

noncomputable section
namespace GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}

theorem tv_mulVec (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x v : Fin n → R) (t : R) :
    (tv σ G x t).mulVec v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  ext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, hf,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => by ring

theorem hf_add_smul_left (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G (v + c • x) y = hf σ G v y + c * hf σ G x y := by
  simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hf_add_smul_right (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G y (v + c • x) = hf σ G y v + σ c * hf σ G y x := by
  simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hf_conj (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) : σ (hf σ G x y) = hf σ G y x := by
  simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.UTrans.Model
