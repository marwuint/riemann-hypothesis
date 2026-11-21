import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepThetaLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExThOfChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicitySpaceThetaMapOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExAtAssembly

theorem exAt_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → HostHyp D → R.IsChainW → R.IsThPW → R.ExAt := by
  intro h1 h2 h3 h4 D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr hH hc hp
  have eP : R.ex_ioP := _root_.GlobalTheory.IndefLinks.exists_ioP_of_realDat D G Pl0 T A Ks R h0 hf hm hp.ωP hp.vP
  have eF : R.ex_thF := _root_.GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak h3 D G Pl0 T A Ks R h0 hf hm hp eP
  exact ⟨_root_.GlobalTheory.Chain.ExItY.ex_ItY_holds h1 h2 D G Pl0 T A Ks R h0 hf hm hH hc, _root_.GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner D G Pl0 T A Ks R h0 hf hm hc,
    _root_.GlobalTheory.Chain.ExIoY.ex_ioY_holds h1 h2 h3 h4 D G Pl0 T A Ks R h0 hf hm hH hc, _root_.GlobalTheory.Twist.LastStepLift.exists_lastStep_lift D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.ProjectedLift.ex_Th_of_chain D G Pl0 T A Ks R h0 hf hm hr, eP, eF,
    _root_.GlobalTheory.Twist.exists_thG_models D G Pl0 T A Ks R h0 hf hm hp.thF eF⟩

end GlobalTheory.ExAtAssembly
