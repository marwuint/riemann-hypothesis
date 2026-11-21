import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

section Family

variable {o : Type*} [DecidableEq o] {m m' : o → Type*}

theorem mdel_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdel (fun x => blockDiagonal' fun i => A i x) z ξ = blockDiagonal' fun i => mdel (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

theorem mdbar_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdbar (fun x => blockDiagonal' fun i => A i x) z ξ =
      blockDiagonal' fun i => mdbar (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]

variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}

theorem isUnit_det_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, IsUnit (A i).det) :
    IsUnit (blockDiagonal' A).det := by
  refine isUnit_det_of_right_inverse (B := blockDiagonal' fun i => (A i)⁻¹) ?_
  rw [← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext i
  exact mul_nonsing_inv _ (h i)

theorem conn_blockDiagonal' (h : ∀ i, IsUnit (H i z).det) (ξ : E) :
    conn (fun x => blockDiagonal' fun i => H i x) z ξ = blockDiagonal' fun i => conn (H i) z ξ := by
  refine (eq_conn_of_compatible (H := fun x => blockDiagonal' fun i => H i x)
    (isUnit_det_blockDiagonal' h) ?_).symm
  rw [mdel_blockDiagonal', blockDiagonal'_transpose, ← blockDiagonal'_mul]
  congr 1
  funext i
  exact conn_transpose_mul (h i) ξ

theorem curv_blockDiagonal' {k : WithTop ℕ∞} (d : ∀ i, MContDiffAt k (H i) z)
    (h : ∀ i, IsUnit (H i z).det) (ξ η : E) :
    curv (fun x => blockDiagonal' fun i => H i x) z ξ η =
      blockDiagonal' fun i => curv (H i) z ξ η := by
  have he : (fun x => conn (fun x => blockDiagonal' fun i => H i x) x ξ) =ᶠ[𝓝 z]
      fun x => blockDiagonal' fun i => conn (H i) x ξ :=
    (eventually_all.2 fun i => (d i).eventually_isUnit (h i)).mono
      fun x hx => conn_blockDiagonal' hx ξ
  rw [curv, mdbar_congr he, mdbar_blockDiagonal' fun i x => conn (H i) x ξ, ← blockDiagonal'_neg]
  rfl

end Family

end GlobalTheory.HermFrame
