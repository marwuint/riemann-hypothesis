import Formalism.PieriBlockIdeals.MertensReciprocalElementary
import Formalism.PieriBlockIdeals.HidaLatticeInclusionAtCoarseWeightBound

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.LargeParameterEstimates

open Classical
open Formalism.CohomologicalDescent.LogSmallConstantBounds

structure Rows (P : Par) (X' A : ℝ) : Prop where
  b'_eq : P.b' = P.x * P.b / X'
  sum_le : X' * (P.S + P.η) ≤ P.b
  kS_le : (P.k : ℝ) * P.S ≤ P.w''
  S_ge : 1 ≤ P.S
  m_ge : 2 ≤ P.m
  f_eq : P.f = 2 * P.n
  f_le : P.f ≤ P.k
  t_le : (P.t : ℝ) ≤ A
  N_le : P.N ≤ A * P.x

structure Big (L x X' A : ℝ) : Prop where
  x_ge : 5 ≤ x
  L_ge : 4 ≤ L
  X1 : 4 * (L + 2) ≤ X'
  X2 : 5.2 * A ^ 3 * x ≤ X'
  X3 : 40 * A ^ 7 * x ^ 2 * L ≤ X'
  b3 : 40 * A ^ 7 * x ^ 2 * L ^ 3 ≤ Real.exp L

def BigEv : Prop :=
  ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    Big (x ^ ε) x (Real.exp (x ^ (ε / 3))) (x ^ C)

def KmaxSize : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    (P.kmax : ℝ) ≤ 2 * P.b / P.lstar ∧
    2 * P.b / P.lstar =
      2 * ((P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
        + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L)) / (P.m : ℝ) ∧
    2 * P.b / P.lstar ≤ 4 * A ^ 4 * P.x * P.L ^ 2 + 2 * A ^ 3 * (P.S + (P.t : ℝ) + P.L) ∧
    2 * P.b / P.lstar + (P.t : ℝ) ≤ A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.S) ∧
    (P.kmax : ℝ) + (P.t : ℝ) ≤ A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.S)

def Small1 : Prop :=
  ∀ (P : Par) (X' A : ℝ) (T : ℕ), P.Hyp → Rows P X' A → Big P.L P.x X' A → T ≤ P.f →
    (P.k : ℝ) * (P.S + 1) ≤ 2 * (P.k : ℝ) * P.S ∧ 2 * (P.k : ℝ) * P.S ≤ 2 * P.w'' ∧
    2 * P.w'' = 2 * P.b / ((P.n : ℝ) * X') ∧
    (T : ℝ) * (2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)) ≤ 8 * (P.L + 2) * P.b / X' ∧
    8 * (P.L + 2) * P.b / X' ≤ 2 * P.b

def Small2 : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    1.3 * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.b' ≤ 5.2 * (P.f : ℝ) * (P.t : ℝ) ^ 2 * P.b' ∧
    5.2 * (P.f : ℝ) * (P.t : ℝ) ^ 2 * P.b' ≤ 5.2 * A ^ 3 * P.x * P.b / X' ∧
    5.2 * A ^ 3 * P.x * P.b / X' ≤ P.b

def Small3 : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    P.S + P.η ≤ P.b / X' ∧
    P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6 ≤ 5 * A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.b / X') ∧
    (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤ 4 * A ^ 3 * P.L ∧
    (P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6) * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤
      20 * A ^ 7 * P.x ^ 2 * P.L * (P.L ^ 2 + P.b / X') ∧
    20 * A ^ 7 * P.x ^ 2 * P.L * (P.L ^ 2 + P.b / X') ≤ P.b

def SmallSum : Prop :=
  ∀ (P : Par) (X' A : ℝ) (T : ℕ), P.Hyp → Rows P X' A → Big P.L P.x X' A → T ≤ P.f →
    (T : ℝ) * (2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)) + 1.3 * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.b'
      + (P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6) * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤ 4 * P.b ∧
    4 * P.b ≤ 2 * (P.m : ℝ) * P.b

def TailInequalitySum : Prop :=
  ∀ (P : Par) (X' A : ℝ) (T : ℕ), P.Hyp → Rows P X' A → Big P.L P.x X' A → T ≤ P.f →
    totalBound P T (30 * (P.m : ℝ) * P.b * P.L ^ 2) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b

def LargeOfRows : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S → 4 * A ^ 4 * P.x ^ 2 * P.L ^ 2 < P.b ^ ((4 : ℝ) / 5) → P.Large

end Formalism.CohomologicalDescent.LargeParameterEstimates
