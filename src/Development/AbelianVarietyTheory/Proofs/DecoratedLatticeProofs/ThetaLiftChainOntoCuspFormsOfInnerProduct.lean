import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCoefVanishesOffLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpannedBySatakeEigenElements
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandra
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainFockVectorLevelLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParametersLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainRealZetaNonvanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardInductionFixedMetric

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_classicalTheorems : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → UpPar D → OntoAll D := by
  intro hHCF hCRD hDSC hHCM hCW D hHF hUP
  have hLF : LevFacts D := _root_.GlobalTheory.ChainOnto.LevelFacts.levFacts D
  have hFD : FinDim D := _root_.GlobalTheory.ChainOnto.finDim_of_levFacts hHCF D hLF
  have hMet : MetEx D := _root_.GlobalTheory.ChainMetric.metEx hCRD D
  have hES : EigSpan D := _root_.GlobalTheory.ChainOnto.eigSpan_of_parts hCRD D hFD hMet hLF
  have hPI : ParIndep D := _root_.GlobalTheory.ChainOnto.parIndep D
  have hPOV : ParOfVal D := _root_.GlobalTheory.ChainOnto.parOfVal_of_parts hCRD D hMet hLF
  have hPB : ParBoundW D := GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound hCRD D hLF
  have hLL : LevelLaw D := _root_.GlobalTheory.ChainOnto.levelLaw D
  have hCS : CoefSupp D := _root_.GlobalTheory.ChainOnto.CoefSuppPf.coefSupp D
  have hArch : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := _root_.GlobalTheory.TwArch.archOnRecord_closed hDSC hHCM D
  have hRZ : RealZeta D := _root_.GlobalTheory.RealZetaProof.realZeta hHCM D hArch
  have hZN : ZetaNe D := _root_.GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real D hMet hLF hLL hCS hRZ
  have hUN : UpNe D := _root_.GlobalTheory.ChainOnto.upNe_of_heckeForm D hHF hMet hLF hZN
  have hUS : UpSpan D := _root_.GlobalTheory.ChainOnto.upSpan_of hDSC hHCM hCRD hCW D hLF hLL
  have hUA : UpAdj D := _root_.GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay hCRD D
  have hSU : StepUp D := _root_.GlobalTheory.ChainOnto.stepUp D hFD hPOV hUS hUA hUP hUN
  have hCL : ChainLW D := _root_.GlobalTheory.ChainOnto.chainLW_holds D
  have hCU : ChainUp D := chainUp_of D hMet hPB hCL hSU
  exact _root_.GlobalTheory.ChainOnto.ontoAll_of_chainUp D hFD hMet hES hPI hCU

end GlobalTheory.ChainOnto
