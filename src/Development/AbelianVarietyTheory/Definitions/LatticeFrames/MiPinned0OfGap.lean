import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.SG.PackageTie2 Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.ConcreteSettingExists

namespace GlobalTheory.Core.Rk

theorem finX_of_gap : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC :=
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc⟩
  Formalism.L2.SG.Pf.finXC_of GlobalTheory.wuDecayOfGap CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

section Worlds

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

end Worlds

end GlobalTheory.Core.Rk

end
