import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField

def MtType {D : D7} (u : D.what₂.Word) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (i : ℕ) (h : i < D.R.m), (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ mt (i + 1) k ^ n = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨i, h⟩) ∧
      ∀ z : unitary D.host.E, ((mt (i + 1) (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

end GlobalTheory.KerJ
