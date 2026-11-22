import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTheoremModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CrysOnLevel

theorem isCrysOn_of_isCrys : ∀ (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) Y.ρ → Formalism.MainNotions.LocalSituation.IsCrysOn (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((HW l).W K s LL h).GKs Y := by
  intro D HW l _ K s LL h Y hY
  exact (GlobalTheory.TorsionBoundCompare.crys_iff D.loc HW (D.locA l) h Y).mpr
    ((_root_.GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (D.loc l) (D.locA l) (D.locT l) K (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.levelField K s) LL h.2.2.1
      Y.V Y.ρ).1 hY)

end GlobalTheory.CrysOnLevel
