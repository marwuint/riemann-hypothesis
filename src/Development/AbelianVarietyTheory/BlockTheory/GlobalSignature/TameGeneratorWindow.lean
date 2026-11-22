import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

section Point

variable {D : D7}

def RankWindowAt (L : SizeData₂ D) : Prop :=
  (L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) ∧ 4 ≤ D.R.n) ∧
  ((L.sc.x * L.sc.delta1) ^ (1 / 2 : ℝ) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ 2 * (L.sc.x * L.sc.delta1) ^ (1 / 2 : ℝ)) ∧
  (L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ (D.R.k : ℝ) ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps))

def CoarseWindowAt (L : SizeData₂ D) : Prop :=
  L.sc.x ^ (1 / 2 - L.sc.eps / 8) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (1 / 2 : ℝ) ∧ 44 ≤ D.R.m ∧
  L.sc.x ^ (2 + 8 * L.sc.eps) / 2 ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) ∧
  (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps)

def TypePrimeWindowAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧
    (D.R.r : ℝ) ^ 4 * (LevelStarExponents.condE D : ℝ) ^ C ≤ Y ^ (1 / 4 : ℝ) ∧ 2 * Y ≤ L.sc.b ^ 9 ∧
    ∀ i : Fin 2, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y

def BelowCutAt (L : SizeData₂ D) : Prop :=
  (D.host.q : ℝ) < L.sc.X' ∧ (D.host.d : ℝ) < L.sc.X' ∧ (D.host.pde : ℝ) < L.sc.X' ∧ (D.host.pde' : ℝ) < L.sc.X' ∧
  L.sc.X' ≤ L.sc.X'' D.R.n ∧ 2 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) + 1 < L.sc.X'

def WindowsAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  RankWindowAt L ∧ CoarseWindowAt L ∧ TypePrimeWindowAt L C ∧ BelowCutAt L

def hWidth (L : SizeData₂ D) : ℝ := L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1

def lJ (L : SizeData₂ D) : ℝ :=
  (D.R.m : ℝ) * L.sc.b * L.sc.x ^ L.sc.eps / ((D.R.k : ℝ) * ((D.R.m : ℝ) + (D.R.t : ℝ)) * Real.log (3 * hWidth L))

def tameList (D : D7) (k : Fin 2) (v : D.nd.PlG k) : Option (Fin D.R.m × Bool) → (ZMod (D.host.g k))ˣ
  | none => 1
  | some (j, true) => D.nd.chiT k v j
  | some (j, false) => (D.nd.chiT k v j)⁻¹

def TameDistinct (D : D7) : Prop := ∀ (k : Fin 2) (v : D.nd.PlG k), Function.Injective (tameList D k v)

def TameInjective (D : D7) : Prop := ∀ (k : Fin 2) (v : D.nd.PlG k), Function.Injective (D.nd.chiT k v)

end Point

theorem TameDistinct.injective {D : D7} (h : TameDistinct D) : TameInjective D := fun k v a b hab => by
  have := h k v (a₁ := some (a, true)) (a₂ := some (b, true)) hab
  simpa using this

theorem lJ_den_pos {D : D7} (L : SizeData₂ D) :
    0 < (D.R.k : ℝ) * ((D.R.m : ℝ) + (D.R.t : ℝ)) * Real.log (3 * hWidth L) := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  push_cast at hk
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hb : 0 < L.sc.b := Real.exp_pos _
  have h1 : 1 < 3 * hWidth L := by
    unfold hWidth
    have := L.Sc_pos
    have := L.etaSz_pos
    linarith
  exact mul_pos (mul_pos (by linarith) (by linarith)) (Real.log_pos h1)

end GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

end
