import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def sgnCN (k r : ℕ) : Fin (2 * r + k + 1) → Bool := fun i =>
  if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

def IsShape (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (bv : ℝ) : Prop :=
  IsHCParam lam ∧ (∀ i, i.val < k - 1 → 0 ≤ lam i ∧ lam i ≤ bv / 8) ∧
    ∀ i, k - 1 ≤ i.val → -(2 * bv) ≤ lam i ∧ lam i ≤ -bv

def IsRange (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c h q : ℝ) : Prop :=
  0 < c ∧ GapAtLeast (sgnCN k r) lam h ∧ 100 * max 1 c * q * Real.sqrt (2 * r + 2) ≤ c * h ∧
    ∀ i j : Fin (2 * r + k + 1), i < j → j.val < k - 1 → 100 * max 1 c * q ≤ lam i - lam j

def dist1 {n : ℕ} (μ lam : Fin n → ℝ) : ℝ := ∑ a, |μ a - lam a|

def InPP {n : ℕ} (lam : Fin n → ℝ) (t : ℝ) (μ : Fin n → ℝ) : Prop :=
  (∀ a, ∃ m : ℤ, μ a - lam a = (m : ℝ)) ∧ dist1 μ lam ≤ t

structure HRep (k r : ℕ) where
  H : Type
  [nG : NormedAddCommGroup H]
  [iP : InnerProductSpace ℂ H]
  σ : Mat k r → (H →L[ℂ] H)

attribute [instance] HRep.nG HRep.iP

variable {k r : ℕ}

def HRep.onJ (A : HRep k r) (P : Mat k r) : Mat k r → (A.H →L[ℂ] A.H) := fun g => A.σ (P⁻¹ * g * P)

def HRep.IsDSAt (A : HRep k r) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ) : Prop :=
  IsDS (sgnCN k r) μ (A.onJ P)

abbrev Idx (k r l : ℕ) := {I : Finset (Fin (2 * r + k + 1)) // I.card = l}

def wtI (dual : Bool) {l : ℕ} (I : Idx k r l) : Fin (2 * r + k + 1) → ℝ :=
  fun a => if a ∈ I.1 then (if dual then -1 else 1) else 0

namespace Ex

open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def detRep (k r : ℕ) (μ : Fin (2 * r + k + 1) → ℝ) : HRep k r where
  H := ℂ
  σ := fun g => (g.det ^ ⌊μ 0⌋₊) • ContinuousLinearMap.id ℂ ℂ

theorem subsingleton_idx_top : Subsingleton (Idx k r (2 * r + k + 1)) :=
  ⟨fun I J => Subtype.ext (by
    rw [(Finset.card_eq_iff_eq_univ I.1).1 (by simpa using I.2),
      (Finset.card_eq_iff_eq_univ J.1).1 (by simpa using J.2)])⟩

attribute [local instance] subsingleton_idx_top

theorem subsingleton_idx_zero : Subsingleton (Idx k r 0) :=
  ⟨fun I J => Subtype.ext ((Finset.card_eq_zero.mp I.2).trans (Finset.card_eq_zero.mp J.2).symm)⟩

attribute [local instance] subsingleton_idx_zero

end Ex

end GlobalTheory.Mom
