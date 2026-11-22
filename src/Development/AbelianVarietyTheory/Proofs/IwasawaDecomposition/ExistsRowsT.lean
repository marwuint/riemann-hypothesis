import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodRowLatticesIntegralProvisionalRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqOverSameChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexZeroOffTwistedPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsReferenceTupleIsometryColumnPairing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsIsometryColumnPairingAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProvisionalRowsFurtherCompatibilitiesAtState
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

set_option maxHeartbeats 4000000 in

theorem exists_rowsT : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w) (x : St P), (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) → ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW := by
  refine StepW.of_all fun K B f T w hK hF hw P x hη => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have h1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ h1.symm
    refine P.exact.trans ?_
    rw [_root_.GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  let t : RowsT K w x.o.Z P.Wt x.s.p0 :=
    { hX := P.hX
      r := x.rowsAre hη
      exAt := x.m.exAt
      inGeo := x.m.inGeo
      grpAt := x.fits.grpAt
      grp := x.fits.grp
      mu :=
        { inj := w.ok.xi_inj
          range := w.xi_range
          mu0 := w.l.xi0
          star := by
            show w.I.xi w.I.muStar = f.del
            rw [w.ok.xi_star, w.C_eq]
          star' := by
            show w.I.xi w.I.muStar' = f.del'
            rw [w.ok.xi_star', w.C_eq]
          tw := P.q.mu.tw
          on := P.q.mu.on
          off := P.q.mu.off
          sub := P.sub
          supp := P.supp }
      exact := hex
      untw := _root_.GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted K B f T w hK hF hw P x hη hex
      emt0 := _root_.GlobalTheory.Mem.R3.Rw.St.eMt0_isometry K B f T w hK hF hw P x hη
      emt := _root_.GlobalTheory.Mem.R3.Rw.EmtTw.eMtTw_isometry_state K B f T w hK hF hw P x hη
      etaF := x.etaF
      rowInt := _root_.GlobalTheory.RowIntQ.rowInt_over K B f T w P x.o
      idx := fun Y _ => (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Y }
  exact ⟨t, _root_.GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state K B f T w hK hF hw P x hη t rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3.Rw.St

end
