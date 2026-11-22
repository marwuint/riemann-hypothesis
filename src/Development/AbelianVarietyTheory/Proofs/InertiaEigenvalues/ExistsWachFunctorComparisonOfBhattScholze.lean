import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwFonCmpTies

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.HWL

theorem exists_hw_fon_cmp_of_integral : GlobalTheory.Published.BhattScholzeIntegral →
    ∀ D : D7, ∃ (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Nonempty (CmpOf D.loc D.locA HW F) := by
  intro hI D
  obtain ⟨H, F, hC, -⟩ := exists_hw_fon_cmp_ties (_root_.GlobalTheory.bhattScholze_coeff hI) D.loc D.locA D.locT
  exact ⟨H, F, hC⟩

end GlobalTheory.HWL
