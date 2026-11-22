import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM
open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RiemInt

open GlobalTheory.RosatiAH GlobalTheory.AppellHumbertTrivial

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : IsFactorAH u Hm χ) (l m : u.Λ) :
    ∃ n : ℤ, (hermForm Hm l m).im = n := by
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hil : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have him : ⊤ ≤ (u.ex (0 + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have hlm : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h.2.2 l i 0 hi
  have h2 := h.2.2 m i _ hil
  have h3 := h.2.2 m i 0 hi
  have h4 := h.2.2 l i _ him
  have hne := u.fr_ne i _ hlm
  have hs : hermForm Hm m l = star (hermForm Hm l m) := by
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.1.eq, Matrix.dotProduct_mulVec]
  have hχl : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  have hχm : χ m ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  rw [h2] at h1
  rw [h4, h1] at h3
  simp only [zero_add, zero_dotProduct, mul_zero] at h3 hne
  rw [add_comm (m : Fin g → ℂ) l] at h3
  unfold hermForm at hs ⊢
  rw [hs] at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h3
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h3 ⊢
  simp only [Complex.exp_add] at h3
  have he : Complex.exp (Real.pi * c) = Complex.exp (Real.pi * star c) := by
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hχl hχm)
      (Complex.exp_ne_zero (Real.pi / 2 * a))) (Complex.exp_ne_zero (Real.pi / 2 * b))) hne) ?_
    linear_combination h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  have hp := Real.pi_pos
  refine mul_left_cancel₀ (a := 2 * Real.pi) (by positivity) ?_
  linear_combination this

variable {g : ℕ}

end GlobalTheory.RiemInt

