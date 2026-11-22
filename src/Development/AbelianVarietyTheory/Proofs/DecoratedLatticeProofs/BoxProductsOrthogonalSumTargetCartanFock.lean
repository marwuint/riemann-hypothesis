import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvolutionOrthDecBlockSumRealMat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOutsideBoxProductOrthDecSumLattice
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

theorem frameLat_selfDual {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem box_sum_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∃ (sB : RealMat B) (LB : Lat B), (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧ IsSelfDualC B LB ∧ (∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA sB (o.boxT A Φ Φ')) ∧ ∀ (LA : Lat A) (Sf : Finset (FinPl D)) Φ Φ', IsSphOff ψ A W LA (frameLat W) Sf Φ → IsSphOff ψ A H LA (frameLat H) Sf Φ' → IsSphOff ψ A B LA LB Sf (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ hW hH
  refine ⟨sumMat o sW sH, sumLatO o (frameLat W) (frameLat H), _root_.GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat D B W H o sW sH hW hH,
    _root_.GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D B W H o _ _ (frameLat_selfDual W) (frameLat_selfDual H),
    fun Φ Φ' h₁ h₂ => _root_.GlobalTheory.Core.Rk.FockBoxT.isFockVec_boxT D ψ θ A B W H o sA sW sH hψ hθ Φ Φ' h₁ h₂,
    fun LA Sf Φ Φ' h₁ h₂ => _root_.GlobalTheory.Core.Rk.SumBoxSph.isSphOff_boxT D ψ A B W H o LA _ _ Sf Φ Φ' h₁ h₂⟩

end GlobalTheory.Core.Rk.SumBox
end
