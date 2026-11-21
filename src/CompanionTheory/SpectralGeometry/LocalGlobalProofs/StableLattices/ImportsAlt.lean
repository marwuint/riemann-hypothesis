import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.UpqRep

namespace GlobalTheory.CompanionTheory.DSCapelliAction

theorem actQ : CompanionTheory.D.DSIC.ActQ := by
  intro n ε H _ _ σ S E h u v
  exact GlobalTheory.CapelliFreeAction.actU_qdet n ε H σ S E (fun a b w => h.act a b w) u v

end GlobalTheory.CompanionTheory.DSCapelliAction
