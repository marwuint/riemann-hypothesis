import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PpPosTypGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalPositivity
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem level_congr_mod_sq (D : D7) (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD Formalism.MainNotions.S.Lat.gS D ^ 2] := by
  have h : Formalism.MainNotions.S.Lat.gS D ^ 2 ∣ D.modT := by unfold Formalism.MainNotions.S.Lat.gS; exact D.gg_dvd_modT
  exact (D.T_modEq_of_dvd u h).trans (D.T_modEq_of_dvd u' h).symm

theorem prodConvNew_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConvNew X u u' ψ := by
  have hg : ∀ v, TypAt X v → 0 < gAt X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos X u u' ψ hψ hs (level_congr_mod_sq D u u') hg
  refine prodConvNew_gen X u u' ψ hb hψ hs hloc fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos X hg v⟩
  by_cases hv : TypAt X v
  · exact pp_pos_typ_gen X hb ψ hψ hs u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord X u u' ψ hψ hs hv l

end Formalism.L2.SG.Pf.ProdConvCut2
