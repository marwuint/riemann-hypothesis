import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Development
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexAStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.InvMulMemOfScaledEntriesCongr
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.XflagEqMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.HTSpanLeft
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.InvSubOneBd
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.PairValG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gval_eq_G (hrows : IsRowReps D F0 what₂) {t : Term D u u' F0 what₂}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} (hrep : Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F') :
    Gval (lf D F0) F' = t.G := by
  obtain ⟨h, hmk⟩ := hrep
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' F0 t.lam (hrows.1 t.lam t.mem)).1
  change _ = Gt t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls
  rw [← hmk]
  exact (Gt_mk hGF ⟨F', h⟩).symm

end Formalism.L2.SG.Pf.PairValG
