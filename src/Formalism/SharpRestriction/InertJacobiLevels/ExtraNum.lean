import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Finset

def massH {R : Ranks} (H : Host R) (M : ℕ) : ℝ :=
  letI := H.cmStar
  Formalism.HermitianLatticesTheory.mass (stdForm H.E M) (stdLat H.E M)

def duStarH {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) : ℝ :=
  massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f) *
    ∏ ρ, dimV (fun i => (((hc ρ).u i : ℚ) : ℝ))

theorem duStarU_eq (D : D7) (u : D.what₂.Word) : duStarU D u = duStarH D.host (D.hcW u) := rfl

theorem duStar_def_iff (D : D7) (u : D.what₂.Word) :
    (((D.mem u).A.duStar : ℕ) : ℝ) = duStarU D u ↔ (((D.mem u).A.duStar : ℕ) : ℝ) = duStarH D.host (D.hcW u) := Iff.rfl

end Formalism.MainNotions.Inhab

end
