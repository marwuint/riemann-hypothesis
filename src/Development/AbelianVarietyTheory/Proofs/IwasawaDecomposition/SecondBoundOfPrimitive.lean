import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SeriesStep
open GlobalTheory.Mem.R3.Tr
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem listPin_oTw (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (c b : ℝ) {I : Type}
    (Lc : Formalism.IndefR.Links.LevCh (Dof x) I) (h : ListPin (Dof x) Lc c b) :
    ListPin (w.st (oTw x N).Z).toD7 (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z Lc) c b := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G) :)), ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact ((hN _ h2) :))⟩

theorem listSt_oTw (cDep : ℝ) (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (x' : St P) (ho : x'.o = oTw x N)
    (hR : HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh))
    (h : ListSt cDep x) : ListSt cDep x' := by
  unfold ListSt
  generalize x'.m.z.R.toRealDat.toLevCh = Lc' at hR ⊢
  revert Lc'
  unfold Dof
  rw [ho]
  intro Lc' hR
  rw [eq_of_heq hR]
  exact listPin_oTw x N hN _ _ _ h

end GlobalTheory.HeightCounting.Up.SeriesStep
