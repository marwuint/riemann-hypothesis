import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfPhAt
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPtW

namespace Formalism.MainNotions.Ext

theorem addPtW_holds : AddPtW :=
  fun p _ g hOk hF σ a b ha hb =>
    formal_group_add_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF σ a b ha hb

theorem mulPtW_holds : MulPtW :=
  fun p _ g hOk c hc σ a ha =>
    formal_group_mul_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 c hc σ a ha

end Formalism.MainNotions.Ext
