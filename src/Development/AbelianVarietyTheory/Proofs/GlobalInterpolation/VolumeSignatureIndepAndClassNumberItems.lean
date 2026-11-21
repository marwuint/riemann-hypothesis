import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndep
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volSigIndep_and_classItemsAt_of_massRatioUnderVolume (hU : ∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) :
    ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  intro D
  refine ⟨?_, _root_.GlobalTheory.classItemsAt_all D _⟩
  have key := _root_.GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep (fun D hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr => by
    have h2 : Conclusion2 D := volumeMass_of_unfolding D (hU D hT)
    rw [_root_.GlobalTheory.Glob.vol_eq_massI_all_sig D hT h2 W P Q hW hs, _root_.GlobalTheory.Glob.vol_eq_massI_all_sig D hT h2 W₀ P₀ Q₀ hW₀ hs₀]
    have e1 := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    have e2 := Formalism.BasicNotions.sig_sum W₀ hW₀ D.host.φ₀
    rw [hs] at e1
    rw [hs₀] at e2
    simp only at e1 e2
    rw [e1, e2, hr])
  exact key D

end GlobalTheory.Glob
