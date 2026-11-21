import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalRingCardinality.DataArith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.CoefGram

theorem posDef_of_hasSignature {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

end GlobalTheory.Core.CoefGram
