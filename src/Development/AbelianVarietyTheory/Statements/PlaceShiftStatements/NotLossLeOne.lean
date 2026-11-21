import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sig_eq {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) : sig G = G.pl.sigma0 sc := rfl

theorem loss_mono {dl : PlL D → ℝ} {B B' : ℝ} (h : Loss dl B) (hB : B ≤ B') : Loss dl B' :=
  ⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') : LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, h⟩ := h
  obtain ⟨y', rfl, h'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases hy : y = 0
  · exact Or.inl (by rw [hy, zero_mul])
  by_cases hy' : y' = 0
  · exact Or.inl (by rw [hy', mul_zero])
  refine Or.inr ?_
  have e : vw w (y * y') = vw w y + vw w y' := by
    rw [vw, vw, vw, ← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul] <;>
      simpa [FractionalIdeal.spanSingleton_eq_zero_iff]
  have a1 := h.resolve_left hy
  have a2 := h'.resolve_left hy'
  rw [e]; push_cast; linarith

end GlobalTheory.SumSize.Model

end
