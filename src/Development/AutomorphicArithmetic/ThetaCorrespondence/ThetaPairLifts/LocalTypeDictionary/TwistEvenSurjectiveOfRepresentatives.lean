import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainSpannedParamsOfValueIndependent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProdu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParams
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferred
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormOfDoubling

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EvenOnto
theorem even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  intro hHC hCusp hDS hHCM hCW hHowe hWeil hSW hSWc hDoub hUnr D
  have hHecke := _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' hWeil hCusp hSW hSWc hDoub hUnr D
  obtain ⟨hFin, hMet⟩ := _root_.GlobalTheory.EvenMetric.finDim_and_metEx hHC hCusp D
  obtain ⟨hEig, hPoV, hInd⟩ := _root_.GlobalTheory.EvenOnto.eig_parOfVal_indep hCusp D hFin hMet
  have hBd := _root_.GlobalTheory.EvenOnto.parBound_of_rapidDecay hCusp D
  obtain ⟨hSpan, hAdj⟩ := _root_.GlobalTheory.EvenOnto.UpLift.upSpan_upAdj hDS hHCM hCusp hCW D
  have hPar := _root_.GlobalTheory.EvenOnto.upPar_of_transfer hCusp hHowe D
  have hRZ := _root_.GlobalTheory.EvenOntoRealZeta.realZeta hDS hHCM D
  have hZN := _root_.GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real D hMet hRZ
  have hNe := _root_.GlobalTheory.EvenOnto.upNe_of_heckeForm D hHecke hMet hZN
  have hStep := _root_.GlobalTheory.EvenOnto.stepUp D hFin hPoV hSpan hAdj hPar hNe
  exact _root_.GlobalTheory.EvenOnto.ontoAll_of D hFin hMet hEig hInd hBd hStep
end GlobalTheory.EvenOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := GlobalTheory.EvenOnto.even_surjective_of_representatives
end
