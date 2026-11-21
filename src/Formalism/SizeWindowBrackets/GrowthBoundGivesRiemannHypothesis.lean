import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.StatementOC
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def psC : AddChar (E0 × H) ℂ where
  toFun g := if g.1.2 = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rcases a with ⟨⟨a1, a2⟩, ah⟩
    rcases b with ⟨⟨b1, b2⟩, bh⟩
    have key : ∀ x y : ZMod 2, (if x + y = 0 then (1 : ℂ) else -1)
        = (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1) := by
      intro x y
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl <;> simp [h11, h10]
    exact key a2 b2

def chpsC : AddChar (E0 × H) ℂ := chC * psC

def Gsig (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (y : ℝ) : ℂ :=
  GPsi D ell 0 y + GPsi D ell psC y - GPsi D ell chC y - GPsi D ell chpsC y

def fPl (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : ℝ := ((PhiSet (H := H)).card : ℝ)

def delta2 (T2 : Finset H) : ℝ := (T2.card : ℝ) / (Fintype.card H : ℝ)

def ThickPartTranslateMean : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (t : H) (A b : ℝ), 0 < A → 0 < b →
    (1 / (Fintype.card H : ℂ)) * ∑ u0 : H, (1 / ((PhiSet (H := H)).card : ℂ)) *
        ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g ∧ IsThickAt T2 u0 (partner t g)),
          ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * (b : ℂ) * GPsi D ell ψ (A / b)
      = ((delta2 T2 * b / 2 : ℝ) : ℂ) * Gsig D ell (A / b)

def topExcess (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
    (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)

def ThinScales (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (X' θ : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, ∀ y : ℝ, X' / 3 ≤ y → ‖GPsi D ell ψ y‖ ≤ y * θ

def LipW (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) : Prop :=
  ∀ (ψ : AddChar (E0 × H) ℂ) (A w w' : ℝ), 0 < A → 0 < w → 0 < w' →
    ‖(w : ℂ) * GPsi D ell ψ (A / w) - (w' : ℂ) * GPsi D ell ψ (A / w')‖ ≤ 3 * A / min w w' * |w - w'|

def DerivInt (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Cd : ℝ) : Prop :=
  (∀ ψ : AddChar (E0 × H) ℂ, ψ ≠ 0 → ∀ y z : ℝ, 1 ≤ y → 1 ≤ z →
      ‖GPsi D ell ψ y - GPsi D ell ψ z‖ ≤ |y - z| * (Real.log (max y z) + Cd + ‖ell ψ‖)) ∧
  (∀ y z : ℝ, 1 ≤ y → 1 ≤ z → |Gz y - Gz z| ≤ Cd * |y - z|)

def ValuesAtX (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (x ε CL : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, (ψ = psC ∨ ψ = chC ∨ ψ = chpsC) →
    ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ell ψ‖ ≤ CL * Real.log x

def NodeSizes {m : ℕ} (T2 : Finset H) (b b' η : ℝ) (w : H → Fin m → E0 × H → ℝ) : Prop :=
  (∀ u0 j ρ, InPhi ρ → 0 < w u0 j ρ) ∧
  (∀ u0 j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + η + 1) ∧
  (∀ u0 j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w u0 j ρ ≤ 2 * b')

def moveCost (x Cd CL : ℝ) : ℝ := Cd + 3 * (Real.log (x + 1) + Cd + CL * Real.log x)

def GrowthInequalityHypotheses (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < b ∧ 0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ 0 ≤ Cd ∧
  (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  NodeSizes T2 b b' η w ∧
  (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N) ∧
  topExcess D N ell TT a w ≤ Err ∧
  ThinScales D ell X' θ ∧ LipW D ell ∧ DerivInt D ell Cd ∧ ValuesAtX D ell x ε CL

def GrowthInequalityExplicit : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ Err + (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ)
        + (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1))

def SmallCosts (x ε f b η θ Cd CL : ℝ) : Prop :=
  moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ 2 * f * (x + 1) * θ ≤ 1 / x ∧ 6 * f * (x + 1) * (η + 1) ≤ b / x

def GrowthInequalityForm : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err → SmallCosts x ε (fPl H) b η θ Cd CL →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (TT.card : ℝ) * m * b / x

end

def SizeWindows (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧ nT2 ≤ n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧
  x * m ≤ k ∧ k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) ∧
  Err ≤ x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))) ∧
  26 ≤ x ^ (3 * ε / 8)

def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)

def LipWAll : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ),
    LipW D ell

def DerivIntAll : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ), DerivInt D ell Cd

end Formalism.LFunctionChainParameters.ThickSetMeanBounds
