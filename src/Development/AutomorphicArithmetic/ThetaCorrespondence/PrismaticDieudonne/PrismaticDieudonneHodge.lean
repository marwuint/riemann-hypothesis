import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDatumBiconnOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumEpsPairingSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismaticDieudonneHodgeOfHodgeTateDatum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FarguesExactness.FarguesExactOfPrismatic

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace UpperTheory.Lit

theorem prismaticDieudonneHodge : GlobalTheory.Published.PrismaticDieudonneHodge := by
  intro p _ C _ _ _ v O _ _ hv _ _ ε hε
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have hs : IsPrimitiveSystem ε := fun n => GlobalTheory.Dieudonne.isPrimitiveRoot_untilt_root hε n
  exact _root_.GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum p C v O hv ε hs (_root_.GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn p C v O hv ε hs
    (hasDatum_biconn_of GlobalTheory.BRing.exists_bFrame GlobalTheory.QLog.WindowMat.window_matrices _root_.GlobalTheory.WinLift.Top.window_lift
      GlobalTheory.DatumOfMatrices.hasDatum_of_matrices p C v O hv ε hs))

theorem farguesExact : GlobalTheory.CompanionTheory.Ar.HT.FarguesExact :=
  PositivityTheory.Tls2.Jfarg.farguesExact_of_hodge prismaticDieudonneHodge

end UpperTheory.Lit

end
