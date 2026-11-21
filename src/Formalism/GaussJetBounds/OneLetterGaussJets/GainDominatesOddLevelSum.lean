import Formalism.GaussJetBounds.OneLetterGaussJets.OddLevelGainSum
import Formalism.GaussJetBounds.StatementA
import Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity
import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.OneLetterRadius
import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight
import Formalism.GaussJetBounds.GaussJetProofs.LemmaRA
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
import Formalism.IncomingBounds.WeightIdentities
import Formalism.GaussJetBounds.StatementJ
import Formalism.GaussJetBounds.GaussJetProofs.TheoremAOneMonomialLogLoss
import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.GaussJetBounds.StatementM
import Formalism.GaussJetBounds.GaussJetProofs.FrameA
import Formalism.GaussJetBounds.GaussJetProofs.Generic
import Formalism.GaussJetBounds.StatementS
import Formalism.GaussJetBounds.StatementU
import Formalism.GaussJetBounds.OneLetterGauss
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
import Formalism.GaussJetBounds.StatementQ
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.MonoShapeTop
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CompanionTheory
import Formalism.GaussJetBounds.GaussJetProofs.OneGauss

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

theorem propSix7 : PropSix7 := proposition_six
theorem gain_dominates_oddLevel_sum : GainDominatesInnerSum := gain_ge_inner_sum
theorem normCor7 : NormCor7 := by
  intro l d _ hl hd he TT nu1 nu2 size k L w E pi y hpi0 hpi1 hk hw hE hD1 hD2 hy
  refine hy.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le ?_)
  have h6 := propSix7 l d hl hd he TT k (fun s => (Dl d TT nu1 size s : ℝ)) w E hk hw hE hD1 hD2
  have hsum : ∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum fun s _ => gain_dominates_oddLevel_sum l d (by omega) TT nu1 nu2 s
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [h6.1, h6.2]
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
