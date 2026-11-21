import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PosCoordNe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

variable {r : ℕ} (X : Data E r)

theorem hC_sum_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  simp only [hermC, Finset.sum_apply, map_sum, Finset.mul_sum]
  calc (∑ a, ∑ b, ∑ i ∈ s, u a * τ (G a b) * conj (f i b))
      = ∑ a, ∑ i ∈ s, ∑ b, u a * τ (G a b) * conj (f i b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ a, ∑ b, u a * τ (G a b) * conj (f i b) := Finset.sum_comm

private theorem hermC_add_left_eq_add (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' w : Fin r → ℂ) :
    hermC τ G (u + u') w = hermC τ G u w + hermC τ G u' w := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hermC_smul_left_eq_smul_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u w : Fin r → ℂ) : hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hermC_finset_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * hermC τ G (v k) w := by
  classical
  induction s using Finset.induction_on
  · simp [hermC]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left_eq_add, hermC_smul_left_eq_smul_mul, ih]

theorem comb_col {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (col (mat x0 τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by
  rw [hermC_finset_sum_smul_left]
  have hab : ∀ a, hermC τ.1 X.Gm (col (mat x0 τ) a) (col (mat x0 τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have h := congrFun (congrFun (ho τ) a) b
    rw [Matrix.diagonal_apply] at h
    exact h
  simp [hab, mul_ite]

private theorem hermC_smul_right_eq_conj_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem comb_comb {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (∑ b, d b • col (mat x0 τ) b) =
      ∑ a, c a * conj (d a) * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  rw [hC_sum_right']
  simp only [hermC_smul_right_eq_conj_mul, comb_col X ho τ c]
  exact Finset.sum_congr rfl fun a _ => by ring

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
