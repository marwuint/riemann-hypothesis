import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeSplitsAlongSourceWitt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeCoreSplitsAlongTargetWitt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeCorePartsMemSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTrivially
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasePointCharacterTrivialOnDepthLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselSecondBasePointCharacterTrivialDepthLattic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem pcBF_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨fun u hu => ?_⟩
  have e1 := ((F.dB ρ h).coordS (G.V (.grid (2 * ρ + 1) 0))).symm_apply_apply u
  have e2 := ((F.dJ ρ h).coordT (F.V₀ ρ)).symm_apply_apply (u ⬝ (F.dB ρ h).j0)
  obtain ⟨s1, -, s3⟩ := _root_.GlobalTheory.AscFin.srcSplit_pcBF D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  obtain ⟨f4, i4⟩ := _root_.GlobalTheory.AscFin.BesIso.splits_iso D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have b := _root_.GlobalTheory.AscFin.pcBF_big_core D hq T L μ0 hL sc G W M hM F hF ρ h _ s3
  refine ⟨u ⬝ (F.dB ρ h).jX, s1, u ⬝ (F.dB ρ h).jY, AddSubgroup.subset_closure ⟨f4, i4⟩,
    (F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0), b.1, (F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0), b.2,
    (F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0), _root_.GlobalTheory.AscFin.latRow_bessel_core_split D hq T L μ0 hL sc G W M hM F hF ρ h _ s3, ?_,
    _root_.GlobalTheory.AscFin.pcBF_xZero_char D hq T L μ0 hL sc G W M hM F hF ρ h u hu, _root_.GlobalTheory.SecondBaseChar.ychar D hq T L μ0 hL sc G W M hM F hF ρ h u hu⟩
  have e2' : (F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0)) = (u ⬝ (F.dB ρ h).j0) := by
    simp only [HypDec.coordT, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e2
    exact (add_right_comm _ _ _).trans e2
  have e1' : (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) + (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) + (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) = u := by
    simp only [HypDec.coordS, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e1
    exact (add_right_comm _ _ _).trans e1
  rw [e2', e1']

end GlobalTheory.AscFin
