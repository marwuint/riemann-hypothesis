import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.BudgetPf
theorem budget_alt : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := fun hH hW _ =>
  Closed.imp (Closed.and (hH 1) hW) fun _ _ _ ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ => by
    obtain ⟨x0, h⟩ := h1.and h2
    exact ⟨83400, by norm_num, x0, fun x hx hle ι p hp i hi Y hY u1 hq =>
      budgetAt p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) hi Y hY u1 hq⟩
end GlobalTheory.CovHt.BudgetPf
end
