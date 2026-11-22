import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Collect

variable {D : D7}

theorem theta_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) : IsThetaFunO ψ S T (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) ih

end GlobalTheory.Core.Rk.Collect

namespace GlobalTheory.Core.Rk.Collect

end GlobalTheory.Core.Rk.Collect
