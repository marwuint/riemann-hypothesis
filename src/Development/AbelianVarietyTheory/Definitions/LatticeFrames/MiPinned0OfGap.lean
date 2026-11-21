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

def World0.ofGap (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : World I l Z := w.withFin (finX_of_gap _ w.S.toSTies h)

theorem World0.ofGap_C (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : (w.ofGap h).C = w.C := rfl

theorem World0.ofGap_toSTies (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : (w.ofGap h).S.toSTies = w.S.toSTies := rfl

theorem World0.bare_ofGap (w : World0 I l Z) (h : GapHyp (I.rec7 l Z)) : (w.ofGap h).bare = w := rfl

end Worlds

end GlobalTheory.Core.Rk

end
