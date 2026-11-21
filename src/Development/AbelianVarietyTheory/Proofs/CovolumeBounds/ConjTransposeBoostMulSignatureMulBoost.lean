import Mathlib

open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace GlobalTheory
namespace MatrixBall

section general

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
lemma norm_toEuclideanLin_le (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ :=
  M.l2_opNorm_mulVec x

lemma dotProduct_mulVec_eq_inner (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ M *ᵥ v = ⟪(toLp 2 v : EuclideanSpace ℂ n), toEuclideanLin M (toLp 2 v)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma inner_conjTranspose_mul (M N : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (Mᴴ * N) y⟫_ℂ = ⟪toEuclideanLin M x, toEuclideanLin N y⟫_ℂ := by
  rw [toLpLin_mul (q := 2), LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

lemma inner_one_sub (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (1 - Mᴴ * M) x⟫_ℂ = ((‖x‖ ^ 2 - ‖toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, inner_conjTranspose_mul, toLpLin_one,
    LinearMap.id_apply, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp

omit [DecidableEq n] in
lemma isHermitian_one_sub [DecidableEq n] (M : Matrix m n ℂ) : (1 - Mᴴ * M).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self M)

lemma posDef_one_sub_conjTranspose_mul {Z : Matrix m n ℂ} (hZ : ‖Z‖ < 1) :
    (1 - Zᴴ * Z).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_one_sub Z) fun v hv => ?_
  rw [dotProduct_mulVec_eq_inner, inner_one_sub]
  have hx : 0 < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by
    rw [norm_pos_iff]; intro h; exact hv (by simpa using h)
  have h1 := norm_toEuclideanLin_le Z (toLp 2 v)
  have h2 : ‖toEuclideanLin Z (toLp 2 v)‖ < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by nlinarith
  have h3 := norm_nonneg (toEuclideanLin Z (toLp 2 v))
  exact_mod_cast (by nlinarith : (0 : ℝ) < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 -
    ‖toEuclideanLin Z (toLp 2 v)‖ ^ 2)

theorem norm_lt_one_of_posDef {Z : Matrix m n ℂ} (hP : (1 - Zᴴ * Z).PosDef) : ‖Z‖ < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Z = 0 := by ext i j; exact hn.elim j
    simp [this]
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one)
    (f := fun x => ‖toEuclideanLin Z x‖)
    ((toEuclideanLin Z).continuous_of_finiteDimensional.norm.continuousOn)
  have hx1 : ‖x‖ = 1 := by simpa using hx
  have hx0 : ofLp x ≠ 0 := by
    intro h
    have : x = 0 := by simpa using h
    simp [this] at hx1
  have h1 := hP.dotProduct_mulVec_pos hx0
  rw [dotProduct_mulVec_eq_inner, inner_one_sub, toLp_ofLp, hx1] at h1
  have h2 : (0 : ℝ) < 1 ^ 2 - ‖toEuclideanLin Z x‖ ^ 2 := by exact_mod_cast h1
  have h3 := norm_nonneg (toEuclideanLin Z x)
  have h4 : ‖toEuclideanLin Z x‖ < 1 := by nlinarith
  refine lt_of_le_of_lt ?_ h4
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm h3 fun y hy => ?_
  exact hmax (by simpa using hy)

theorem posDef_iff_norm_lt_one (Z : Matrix m n ℂ) : (1 - Zᴴ * Z).PosDef ↔ ‖Z‖ < 1 :=
  ⟨norm_lt_one_of_posDef, posDef_one_sub_conjTranspose_mul⟩

end general

end MatrixBall

end GlobalTheory
