import Mathlib
import Formalism.PieriBlockIdeals.Statement
import Formalism.RankGapBounds.CloudMinFalse
import Formalism.PieriBlockIdeals.StatementLA

open MvPolynomial CategoryTheory TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.SL2BinomialLattices

open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA

universe u v u' v'

def LgLog : Prop :=
  ∀ l y : ℕ, (Nat.log l y : ℝ) * Real.log l ≤ Real.log y

structure Shape (N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ) : Prop where
  anti : StrictAnti U
  inRange : ∀ a, 0 ≤ U a ∧ U a ≤ (h : ℤ)
  k_le : k ≤ N
  cloudIn : ∀ a : Fin N, a.val < k → xm ≤ U a ∧ U a ≤ xm + (S : ℤ)
  restIn : ∀ a : Fin N, k ≤ a.val → lo ≤ U a ∧ U a ≤ lo + (eta : ℤ)

def eCl {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => p.2.val < k), Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat

def eRest {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => k ≤ p.1.val), Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat

def eCross {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val),
    Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat

def ESplit3 : Prop :=
  ∀ (N k l : ℕ) (U : Fin N → ℤ), eExp U l = eCl U k l + eRest U k l + eCross U k l

def ChooseSplit : Prop :=
  ∀ N k : ℕ, k ≤ N →
    k.choose 2 + (N - k).choose 2 + k * (N - k) = N.choose 2 ∧
    ((posPairs N).filter (fun p => p.2.val < k)).card = k.choose 2 ∧
    ((posPairs N).filter (fun p => k ≤ p.1.val)).card = (N - k).choose 2 ∧
    ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)).card = k * (N - k)

def ThreeBounds : Prop :=
  ∀ (l N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime → Shape N k h S eta xm lo U →
    eCl U k l ≤ k.choose 2 * Nat.log l S ∧ (S ≤ l → eCl U k l = 0) ∧
    eRest U k l ≤ (N - k).choose 2 * Nat.log l eta ∧ (eta ≤ l → eRest U k l = 0) ∧
    eCross U k l ≤ k * (N - k) * Nat.log l h ∧
    k * (N - k) * Nat.log l h ≤ k * (N - k) * Nat.log l (2 * h + N)

def SizeLarge : Prop :=
  ∀ (l N k h S eta ex m t : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime →
    Shape N k h S eta xm lo U → ex ≤ eExp U l → eta ≤ l → N - k ≤ m + t →
    (ex : ℝ) * Real.log l ≤
        (k : ℝ) * ((N - k : ℕ) : ℝ) * Real.log h + (k.choose 2 : ℝ) * Real.log S ∧
      (k : ℝ) * ((N - k : ℕ) : ℝ) * Real.log h + (k.choose 2 : ℝ) * Real.log S ≤
        (k : ℝ) * ((m : ℝ) + t) * Real.log (3 * (h : ℝ)) + (k : ℝ) ^ 2 * Real.log ((S : ℝ) + k)

end Formalism.CohomologicalDescent.SL2BinomialLattices
