import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParams
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalLocTripleWithLocalization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvLgGFieldOfSmallField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonemptyTwOf
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.TwInputs.AtLayer
end GlobalTheory.TwInputs.AtLayer
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem nonempty_twOf_of_law_rx_colPin : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  intro hP hS hL _
  have e1 := (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  have e2 := EvG.inter (_root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members hP hS hL) (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP)
  refine (e1.inter e2).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hV, hH⟩, hG, hF⟩ := H
  refine (hG.inter hF).imp fun B f T hO G hK _ w Z Wt p0 t nch n xd c ⟨e⟩ hR hC => ?_
  exact _root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_hecke_stable_reads (hH := (hH (w.st Z) hO).1) (hV := (hV (w.st Z) hO).1) (hs := (hV (w.st Z) hO).2) e.1
    ((G.2 hK T w Z).1 _ t.r.z.lev.C) (G.1 hK w Z Wt p0 t nch n xd c ⟨e.1⟩ hR hC) (_root_.GlobalTheory.HeckeFamRead.exists_family_reads hP.decay hS.hkTr hS.hkRead)
end GlobalTheory.TwInputs.AtLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_twOf_of_extensionWithLaw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  exact @_root_.GlobalTheory.TwInputs.AtLayer.nonempty_twOf_of_law_rx_colPin
end
end
