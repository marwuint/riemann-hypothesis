import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.Transport

variable {n : ℕ}

theorem conj_lie {A B G G' Y : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hY : Y ∈ lieOf G) :
    B * Y * A ∈ lieOf G' := by
  have hY' : Yᴴ * G + G * Y = 0 := hY
  show (B * Y * A)ᴴ * G' + G' * (B * Y * A) = 0
  rw [← hG]
  calc (B * Y * A)ᴴ * (Aᴴ * G * A) + Aᴴ * G * A * (B * Y * A)
      = Aᴴ * Yᴴ * (A * B)ᴴ * G * A + Aᴴ * G * (A * B) * Y * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * (Yᴴ * G + G * Y) * A := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY']; simp

theorem conj_UH {A B G G' g : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    B * g * A ∈ Formalism.QuantumDeterminants.UH G' := by
  have hg' : gᴴ * G * g = G := hg
  show (B * g * A)ᴴ * G' * (B * g * A) = G'
  rw [← hG]
  calc (B * g * A)ᴴ * (Aᴴ * G * A) * (B * g * A)
      = Aᴴ * (gᴴ * (A * B)ᴴ * G * (A * B) * g) * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, hg']

theorem prod_conj {Q : Mx n} (h1 : Q⁻¹ * Q = 1) (h2 : Q * Q⁻¹ = 1) (l : List (Mx n)) :
    (l.map fun x => Q * x * Q⁻¹).prod = Q * l.prod * Q⁻¹ := by
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc Q * a * Q⁻¹ * (Q * l.prod * Q⁻¹) = Q * a * (Q⁻¹ * Q) * l.prod * Q⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exp_smul_conj {Q : Mx n} (hQ : IsUnit Q) (X : Mx n) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Q⁻¹)) = Q * NormedSpace.exp (t • X) * Q⁻¹ := by
  rw [← Matrix.exp_conj Q _ hQ, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.TypeSum.Transport
