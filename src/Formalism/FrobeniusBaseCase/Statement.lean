import Mathlib

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

def qnum (l : ℕ) : ℝ := (l : ℝ) ^ 2

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def sg (l i : ℕ) : ℝ := 3 / (8 * (l : ℝ) ^ i)

def r1 (l i : ℕ) : ℝ := rho l + 1 / (2 * (l : ℝ) ^ i)

def Kn (i : ℕ) : ℕ := (i + 1) / 2

def s0 (i : ℕ) : ℕ := (i - 1) / 2

def eNum (l s : ℕ) : ℕ := ((l ^ 2) ^ s - 1) / (l ^ 2 - 1)

def SqMulIdentity : Prop := ∀ l : ℕ, 2 ≤ l → qnum l * rho l - 1 = rho l

def PowMulThreeEighthsIdentity : Prop := ∀ l i : ℕ, 2 ≤ l → Odd i → qnum l ^ Kn i * sg l i = 3 * (l : ℝ) / 8

def IdE : Prop := ∀ l s : ℕ, 2 ≤ l →
  eNum l 0 = 0 ∧ eNum l (s + 1) = 1 + l ^ 2 * eNum l s ∧ eNum l s * (l ^ 2 - 1) + 1 = (l ^ 2) ^ s

variable {k : Type*} [Field k] {Z : Type*} {C : Type*}

def HasWt (v : AddValuation k (WithTop ℝ)) (r w : ℝ) (f : MvPowerSeries Z k) : Prop :=
  ∀ A : Z →₀ ℕ, (w : WithTop ℝ) ≤ v (coeff A f) + (((A.degree : ℕ) : ℝ) * r : ℝ)

def OrdGE (n : ℕ) (f : MvPowerSeries Z k) : Prop :=
  ∀ A : Z →₀ ℕ, A.degree < n → coeff A f = 0

def NoConst (t : C → MvPowerSeries Z k) : Prop := ∀ c, OrdGE 1 (t c)

def frob (N : ℕ) (f : MvPowerSeries Z k) : MvPowerSeries Z k :=
  fun B => if ∀ d, N ∣ B d then (coeff (B.mapRange (· / N) (Nat.zero_div N)) f) ^ N else 0

structure Data (k : Type*) [Field k] (Z : Type*) (C : Type*) where

  v : AddValuation k (WithTop ℝ)

  l : ℕ
  l_prime : l.Prime
  l_ge : 3 ≤ l
  v_l : v (l : k) = 1

  i : ℕ
  i_odd : Odd i

  good : C → Prop

  lev : C → ℕ
  pure_good : ∀ c, lev c < Kn i → good c

  ι : Z → C
  ι_inj : Function.Injective ι
  ι_lev : ∀ d, lev (ι d) = 0

  al : C → ℕ → C → k

  g : C → C → k

  lam : C → C → k
  al_all : ∀ (c : C) (j : ℕ) (b : C), ((-(j : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c j b)
  al_good : ∀ c, good c → ∀ (j : ℕ) (b : C), 1 ≤ j → ((-((j : ℝ) - 1) : ℝ) : WithTop ℝ) ≤ v (al c j b)
  al_one : ∀ c, good c → ∀ b, al c 1 b = 0
  al_two : ∀ c, lev c < Kn i → ∀ b, al c 2 b = (l : k)⁻¹ * (g c b + (l : k) * lam c b)
  g_int : ∀ c b, 0 ≤ v (g c b)
  lam_int : ∀ c b, 0 ≤ v (lam c b)

  g_supp : ∀ c, lev c + 1 < Kn i → ∀ b, lev b ≠ lev c + 1 → g c b = 0

namespace Data

variable [Fintype Z] [Fintype C] (D : Data k Z C)

def K : ℕ := Kn D.i

def q : ℕ := D.l ^ 2

def rad : ℝ := rho D.l + sg D.l D.i

def top : ℝ := 1 + rho D.l

def Wt (w : ℝ) (f : MvPowerSeries Z k) : Prop := HasWt D.v D.rad w f

def zvec : C → MvPowerSeries Z k := fun b => ∑ d, if D.ι d = b then X d else 0

def m : ℕ → C → MvPowerSeries Z k
  | 0 => D.zvec
  | s + 1 => fun b => MvPowerSeries.C (-(D.l : k)⁻¹) *
      ∑ c, frob D.q (m s c) * MvPowerSeries.C (D.g c b)

def PsiPartial (N : ℕ) (t : C → MvPowerSeries Z k) : C → MvPowerSeries Z k := fun b =>
  D.zvec b - ∑ c, ∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j)

def Psi (t : C → MvPowerSeries Z k) : C → MvPowerSeries Z k := fun b A =>
  coeff A (D.zvec b) -
    ∑ c, ∑ j ∈ Finset.Icc 1 A.degree, D.al c j b * coeff A (t c ^ (D.l ^ j))

def InWTo (J : ℕ) (t : C → MvPowerSeries Z k) : Prop :=
  (∀ c, D.lev c < J → D.Wt D.top (t c - D.m (D.lev c) c)) ∧
  (∀ c, J ≤ D.lev c → D.Wt D.top (t c))

def PsiIsLimit : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t →
  ∀ (b : C) (A : Z →₀ ℕ) (N : ℕ), A.degree ≤ N →
    coeff A (D.Psi t b) = coeff A (D.PsiPartial N t b)

end Data

end

end Formalism.BaseCaseIdentities
