import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBoundTwo

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem NE_pow (D : D7) : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) = (gS D : ℝ) ^ (D.R.m * D.R.f) := by
  unfold NE
  rw [j_finrank D, ← pow_mul]
  congr 1
  have h2 := D.R.two_le_m
  obtain ⟨k, hk⟩ := D.R.m_even
  have hm : 2 * (D.R.rS + 1) = D.R.m := by
    unfold Ranks.rS
    omega
  rw [← hm]
  ring

end Formalism.MainNotions.GramProductBounds

end
