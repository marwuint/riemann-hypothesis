import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_wRow_lb {D : D7} (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂) :
    ∃ m : ℝ, 0 < m ∧ ∀ Λ ∈ what₂, m ≤ wRow D F0 Λ := by
  rcases what₂.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · refine ⟨what₂.inf' h (wRow D F0), ?_, fun Λ hΛ => Finset.inf'_le _ hΛ⟩
    rw [Finset.lt_inf'_iff]
    exact fun Λ hΛ => Formalism.L2.SG.PairVal.wRow_pos D F0 (hA Λ hΛ)

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

end Formalism.L2.SG.RowsAbsX
