import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLattices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPiecesMutualAnnihilators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCorePieceNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem piecesFB_is_and_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨f1, f2, f3, f4⟩ := _root_.GlobalTheory.AscFin.pcFB_fin D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨g1, g2, g3⟩ := _root_.GlobalTheory.AscFin.AnnPieces.pcFB_dualA D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨b1, b2⟩ := _root_.GlobalTheory.AscFin.DualParts.pcFB_dual D hq T L μ0 hL sc G W M hM F hF σ h h'
  exact ⟨⟨f1, g1, f2, f3, g2, g3, b1, b2, _root_.GlobalTheory.UniStepFB.psiUni_pcFB D hq T L μ0 hL sc G W M hM F hF σ h h', f4, _root_.GlobalTheory.AscFin.PcFBVac.pcFB_vac D hq T L μ0 hL sc G W M hM F hF σ h h'⟩,
    _root_.GlobalTheory.AscFin.SplitsFB.splits_FB D hq T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin
