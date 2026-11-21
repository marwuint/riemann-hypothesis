import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions

structure Scales (la : ℝ) where
  J : ℝ
  one_le_J : 1 ≤ J
  Win : Set ℝ
  windows : ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ Win

namespace Scales

variable {la : ℝ}

def Mem (S : Scales la) (s : Scale) : Prop := s.J = S.J ∧ s.x ∈ S.Win

theorem unb (S : Scales la) (hla : 1 ≤ la) (y : ℝ) : ∃ x ∈ S.Win, y ≤ x := by
  obtain ⟨Y, hY, hW⟩ := S.windows (max y 1)
  have h1 : 1 ≤ Y := le_trans (le_max_right y 1) hY
  refine ⟨Y, hW Y le_rfl ?_, le_trans (le_max_left y 1) hY⟩
  calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
    _ ≤ Y ^ la := Real.rpow_le_rpow_of_exponent_le h1 hla

def scale (S : Scales la) (x eps : ℝ) (hx : 1 < x) (h0 : 0 < eps) (h1 : eps < 1 / 52) : Scale :=
  ⟨x, eps, hx, h0, h1, S.J, S.one_le_J⟩

end Scales

end GlobalTheory.EX

end
