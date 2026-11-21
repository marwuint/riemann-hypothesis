import Mathlib

open Filter Set

namespace KStar.Consta

structure Params where

  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52

  Ct : ℝ
  Ct_nonneg : 0 ≤ Ct

  Cc : ℝ

  q : ℕ
  q_pos : 0 < q

  K : ℝ
  one_le_K : 1 ≤ K

noncomputable instance : Inhabited Params :=
  ⟨{ eps := 1 / 100, eps_pos := by norm_num, eps_lt := by norm_num, Ct := 401,
     Ct_nonneg := by norm_num, Cc := 1, q := 1, q_pos := one_pos, K := 1, one_le_K := le_rfl }⟩

namespace Params

variable (P : Params)

noncomputable def h : ℝ := 2 + 8 * P.eps

noncomputable def Y (X : ℝ) : ℝ := X ^ (1 / P.K)

def Unif (p : ℝ → ℝ → Prop) : Prop :=
  ∀ᶠ X in atTop, ∀ x ∈ Icc (P.Y X) X, p X x

theorem Unif.mono {P : Params} {p r : ℝ → ℝ → Prop} (hp : P.Unif p)
    (h : ∀ X x, x ∈ Icc (P.Y X) X → p X x → r X x) : P.Unif r :=
  Filter.Eventually.mono hp fun X hX x hx => h X x hx (hX x hx)

end Params

end KStar.Consta
