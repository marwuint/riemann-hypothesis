import Mathlib

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_mul_map_det_eq_one_of_sesq {E : Type*} [Field E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (σ : E →+* E) (H : V →ₗ[E] V →ₛₗ[σ] E)
    (hH : ∀ x, (∀ y, H x y = 0) → x = 0) (g : V →ₗ[E] V)
    (hg : ∀ x y, H (g x) (g y) = H x y) :
    LinearMap.det g * σ (LinearMap.det g) = 1 := by
  classical
  let b := Module.finBasis E V
  let S : Matrix _ _ E := Matrix.of fun i j => H (b i) (b j)
  let G := LinearMap.toMatrix b b g
  have hgb : ∀ j, g (b j) = ∑ i, G i j • b i := by
    intro j
    simp only [G, LinearMap.toMatrix_apply]
    exact (b.sum_repr (g (b j))).symm
  have hS : G.transpose * S * σ.mapMatrix G = S := by
    ext i j
    have h1 : S i j = H (g (b i)) (g (b j)) := (hg _ _).symm
    rw [h1, hgb, hgb]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvS⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv
    have hx : ∑ i, v i • b i = 0 := by
      apply hH
      have : H (∑ i, v i • b i) = 0 := by
        apply b.ext
        intro j
        have := congrFun hvS j
        simpa [Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply] using this
      intro y
      rw [this]; rfl
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx i
  have hd := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  have hG : G.det = LinearMap.det g := LinearMap.det_toMatrix b g
  rw [hG] at hd
  apply mul_left_cancel₀ hdet
  linear_combination hd

end GlobalTheory.CompanionTheory.Ar.Flat
