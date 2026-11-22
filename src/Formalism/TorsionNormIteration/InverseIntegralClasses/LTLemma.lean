import Formalism.FormalGroupLog.Statement
import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.LTL

open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP

section Near

variable {K : Type u} [NormedField K] {ι : Type*}

def Near (k : ℕ) (A B : MvPowerSeries ι K) : Prop := Low k A ∧ Low k B ∧ Low (k + 1) (A - B)

theorem Near.of_eq {k k' : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (hk : k = k') :
    Near k' A B := hk ▸ h

theorem Near.mul {k l : ℕ} {A B C D : MvPowerSeries ι K} (h1 : Near k A B) (h2 : Near l C D) :
    Near (k + l) (A * C) (B * D) := by
  refine ⟨h1.1.mul h2.1, h1.2.1.mul h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + B * (C - D) := by ring
  rw [e]
  exact ((h1.2.2.mul h2.1).mono (by omega)).add ((h1.2.1.mul h2.2.2).mono (by omega))

theorem near_one : Near 0 (1 : MvPowerSeries ι K) 1 :=
  ⟨low_zero _, low_zero _, fun d _ => by simp⟩

theorem Near.pow {k : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (n : ℕ) :
    Near (k * n) (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using near_one
  | succ n ih => rw [pow_succ, pow_succ]; exact (ih.mul h).of_eq (by ring)

end Near

section Master

variable {K : Type u} [NormedField K] {ι : Type*}

def Ep (e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) x

def Ldef (e e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  Ep e' x - e.subst x

end Master

section Cong

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

lemma norm_finsum_le' {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

theorem dv_add {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : DivByMv c B) :
    DivByMv c (A + B) := fun d => by
  rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA d) (hB d))

theorem dv_mul {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : IntegralMv B) :
    DivByMv c (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun p _ => ?_
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 A‖ * ‖MvPowerSeries.coeff p.2 B‖ ≤ ‖c‖ * 1 :=
        mul_le_mul (hA _) (hB _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _

def Cong (c : K) (A B : MvPowerSeries ι K) : Prop :=
  IntegralMv A ∧ IntegralMv B ∧ DivByMv c (A - B)

theorem Cong.mul {c : K} {A B C D : MvPowerSeries ι K} (h1 : Cong c A B) (h2 : Cong c C D) :
    Cong c (A * C) (B * D) := by
  refine ⟨integral_mul h1.1 h2.1, integral_mul h1.2.1 h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + (C - D) * B := by ring
  rw [e]
  exact dv_add (dv_mul h1.2.2 h2.1) (dv_mul h2.2.2 h1.2.1)

theorem cong_one (c : K) : Cong c (1 : MvPowerSeries ι K) 1 :=
  ⟨integral_one, integral_one, fun d => by simp⟩

theorem Cong.pow {c : K} {A B : MvPowerSeries ι K} (h : Cong c A B) (n : ℕ) :
    Cong c (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using cong_one c
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

end Cong

section Constr

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

def lin (a : ι → K) : MvPowerSeries ι K := ∑ i, a i • MvPowerSeries.X i

def corr (e e' : PowerSeries K) (π : K) (N : ℕ) (P : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun d => if d.degree = N + 1 then MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1)) else 0

variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}

end Constr

end Formalism.LT.LTL

namespace Formalism.LT

end Formalism.LT
