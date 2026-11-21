import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Module Matrix

namespace Formalism.L2.Geo.Def.G1

section Coord

variable {K : Type} [Field K] [StarRing K]

def IsFrame {n k : ℕ} (H : Matrix (Fin n) (Fin n) K) (g w : Fin k → Fin n → K) : Prop :=
  ∀ a b, ∑ i, g i a * ∑ c, star (w i c) * H c b = if a = b then 1 else 0

theorem IsFrame.map {n k : ℕ} {H : Matrix (Fin n) (Fin n) K} {g w : Fin k → Fin n → K} (hf : IsFrame H g w)
    {A : Type} [CommRing A] (φ : K →+* A) (σ : A →+* A) (hσ : ∀ x, σ (φ x) = φ (star x)) (z : Fin n → A) :
    z = ∑ i, Formalism.UG.hform σ (H.map φ) (fun c => φ (w i c)) z • (fun a => φ (g i a)) := by
  funext a
  have e1 : ∀ d, φ (∑ i, g i a * ∑ c, star (w i c) * H c d) = if a = d then 1 else 0 := fun d => by
    rw [hf a d]; split_ifs <;> simp
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Formalism.UG.hform, Matrix.map_apply, hσ]
  calc z a = ∑ d, z d * (if a = d then 1 else 0) := by simp
    _ = ∑ d, z d * φ (∑ i, g i a * ∑ c, star (w i c) * H c d) := by simp only [e1]
    _ = _ := by
      simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Coord

end Formalism.L2.Geo.Def.G1
