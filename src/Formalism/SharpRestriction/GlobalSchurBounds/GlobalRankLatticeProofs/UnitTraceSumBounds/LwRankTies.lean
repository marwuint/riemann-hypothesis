import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.SharpRestriction.GlobalSchurBounds.AdmittedWeylDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLz

noncomputable section

namespace Formalism.MainNotions.Ext.Lw

open Formalism.BasicNotions Formalism.MainNotions

theorem splitsF_g_all (D : D7) : ∀ j, StandardLattice.SplitsF D (D.host.g j) := fun j => J.splitsF_g D j

theorem splitsF_T_all (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := J.level_prime_splits_totally_real D u

theorem rank_conditions_iff_lowest_space {eps : ℝ} (Fm : FamP eps) :
    RankTiesF Fm ↔ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u := by
  unfold RankTiesF
  constructor
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i u => ((hx0 x hx i).2 u).2⟩
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => ⟨splitsF_g_all (Fm.D x i), fun u => ⟨splitsF_T_all (Fm.D x i) u, hx0 x hx i u⟩⟩⟩

theorem rank_conditions_of_lowest_space {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u) : RankTiesF Fm :=
  (rank_conditions_iff_lowest_space Fm).2 h

end Formalism.MainNotions.Ext.Lw

end
