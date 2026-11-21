import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholze
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOf

namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem exists_hw_fon_cmp_ties : GlobalTheory.Published.BhattScholzeCrystallineLattices →
    ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
      (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) →
      ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) ∧ Nonempty (Formalism.MainNotions.LocalSituation.Ties L A H F) := by
  intro hBS L A hT
  obtain ⟨H, F, hC⟩ := _root_.GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf L A hT (fun l _ => _root_.GlobalTheory.WachLattice.main hBS l (L l) (A l) (hT l))
  exact ⟨H, F, hC, ⟨⟨fun l _ => Classical.choice (GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod l (L l) (A l) (hT l))⟩⟩⟩

end GlobalTheory.HWL
