import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.Columns.InputsWeyl
import Mathlib
import Formalism.GL3MeanSquares.UnitaryConjugateDiagonalMoments

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColOpen

open Formalism.BasicNotions Formalism.L2.Col Formalism.LogVandermondeBounds.StandardLattice Formalism.HermitianLattices.FormalDegreeBoundsAlt

variable {X : Fields} {Pr : Primes X} {R : Ranks}

section Seq

variable (W : Wts X Pr.Word R)

def vSeq (τ : X.Tau) : ℕ → ℝ := fun i => if h : i < R.k - 1 then (((W.row τ).v ⟨i, h⟩ : ℚ) : ℝ) else 0

end Seq

structure Grid (W : Wts X Pr.Word R) (Δ S : ℝ) (c : X.Tau → ℝ) (code : Pr.Word → ℕ → ℕ) : Prop where
  one_le_Δ : 1 ≤ Δ
  S_eq : S = (R.k : ℝ) * (4 * Δ)
  cloud : ∀ τ i, i < R.k - 1 → vSeq W τ i = cloudV (c τ) Δ i
  cloud_nonneg : ∀ τ i, i < R.k - 1 → 0 ≤ vSeq W τ i
  cloud_le : ∀ τ i, i < R.k - 1 → vSeq W τ i ≤ S
  word : ∀ u τ l, l < R.k - 2 → hcSeq W u τ (l + 1) = vSeq W τ l - 1 / 2 - (code u l : ℝ) * Δ
  code_le : ∀ u l, code u l ≤ 1

structure Ends (W : Wts X Pr.Word R) (a b' S : ℝ) : Prop where
  top : ∀ u, ∀ τ ∈ W.tops, a ≤ (W.aTop u τ : ℝ) ∧ (W.aTop u τ : ℝ) ≤ a * (1 + 1 / (R.k : ℝ)) ∧
    b' ≤ (W.bTop u τ : ℝ) ∧ (W.bTop u τ : ℝ) ≤ 2 * b'
  b'_le : 2 * b' ≤ a / 4
  oth_first : ∀ u τ, τ ∉ W.tops → S ≤ hcSeq W u τ 0 - vSeq W τ 0 ∧ hcSeq W u τ 0 - vSeq W τ 0 ≤ 2 * S
  oth_last : ∀ u τ, τ ∉ W.tops → hcSeq W u τ (R.k - 1) = vSeq W τ (R.k - 2) - 1 / 2
  kS_le : (R.k : ℝ) * S ≤ b'

end Formalism.L2.GlobalTheoryTheory.ColOpen
