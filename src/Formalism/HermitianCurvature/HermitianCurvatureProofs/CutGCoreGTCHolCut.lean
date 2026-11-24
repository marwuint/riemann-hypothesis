module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def GTCRef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e0 ∧ KapF P Bs d e0 ∧
      ∃ A0 B0 : M.Ty P → ℂ → ℂ, SmAB P A0 B0 ∧ ConnF P Bs d e0 A0 B0 ∧
        (∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A0 ρ w) ζ).re = 0) ∧
        ∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A0 ρ w) 0 R).im = Real.pi * n

def GTCPhaseRel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      IsFrameB P Bs e0 → KapF P Bs d e0 →
      ∃ u : M.Ty P → ℂ → ℂ, (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) ∧
        ∀ ρ, ∀ ζ ∈ Ann P, e ρ ζ = u ρ ζ • e0 ρ ζ

def GTCConnUniq : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
      ∀ A B A' B' : M.Ty P → ℂ → ℂ, SmAB P A B → SmAB P A' B' → ConnF P Bs d e A B → ConnF P Bs d e A' B' →
        ∀ ρ, ∀ ζ ∈ Ann P, A ρ ζ = A' ρ ζ

def GTCConnPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (A B u : M.Ty P → ℂ → ℂ), SmAB P A B →
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) →
      ConnF P Bs d e A B →
      SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) ∧
      ConnF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
        (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ)

def GTCPhHol : Prop :=
  ∀ (TT : ℝ) (u : ℂ → ℂ), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → ‖u ζ‖ = 1) →
    ∀ R : ℝ, 0 < R → TT < R ^ 2 → ∃ n : ℤ, (circleIntegral (fun w => star (u w) * NF.dZ u w) 0 R).im = Real.pi * n

def GTCPhCurv : Prop :=
  ∀ (TT : ℝ) (u : ℂ → ℂ), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → ‖u ζ‖ = 1) →
    ∀ ζ : ℂ, TT < Complex.normSq ζ → (NF.dZb (fun w => star (u w) * NF.dZ u w) ζ).re = 0

theorem ann_isOpen (P : M.Par) : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq

theorem sphere_sub_ann (P : M.Par) {R : ℝ} (hR0 : 0 < R) (hR : P.TT < R ^ 2) :
    Metric.sphere (0 : ℂ) R ⊆ Ann P := by
  intro w hw
  have h : ‖w‖ = R := by simpa using hw
  show P.TT < Complex.normSq w
  rwa [Complex.normSq_eq_norm_sq, h]

theorem trR_congr {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (h : ∀ ρ, ∀ ζ ∈ Ann P, e ρ ζ = e' ρ ζ) :
    trR P Bs e = trR P Bs e' := by
  funext Φ ρ
  unfold trR rawR
  congr 1
  funext q
  rw [h ρ q.1.2 q.2.2]

theorem tt_nonneg_of_hyp {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'} {d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))}
    (h : GTHyp P Bs X d) : 0 ≤ P.TT := by
  have hOK := h.1.1
  exact (mul_pos hOK.T_pos hOK.T'_pos).le

theorem gauge_rel (hRef : GTCRef) (hPR : GTCPhaseRel) (hU : GTCConnUniq) (hCP : GTCConnPhase)
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hyp : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (A B : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hConn : ConnF P Bs d e A B) :
    ∃ (A0 : M.Ty P → ℂ → ℂ) (u : M.Ty P → ℂ → ℂ),
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A0 ρ) (Ann P)) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => star (u ρ ζ) * NF.dZ (u ρ) ζ) (Ann P)) ∧
      (∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A0 ρ w) ζ).re = 0) ∧
      (∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A0 ρ w) 0 R).im = Real.pi * n) ∧
      ∀ ρ, ∀ ζ ∈ Ann P, A ρ ζ = A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ := by
  obtain ⟨e0, he0, hk0, A0, B0, hAB0, hConn0, hcurv, hhol⟩ := hRef Wp Wq P Bs X d hyp
  obtain ⟨u, hu, heu⟩ := hPR Wp Wq P Bs X d hyp e e0 he hk he0 hk0
  obtain ⟨hAB1, hConn1⟩ := hCP Wp Wq P Bs X d hyp e0 A0 B0 u hAB0 hu hConn0
  have htr : trR P Bs (fun ρ ζ => u ρ ζ • e0 ρ ζ) = trR P Bs e :=
    trR_congr P Bs _ _ (fun ρ ζ hζ => (heu ρ ζ hζ).symm)
  have hConn1' : ConnF P Bs d e (fun ρ ζ => A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B0 ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
    unfold ConnF at hConn1 ⊢
    rwa [← htr]
  have hA := hU Wp Wq P Bs X d hyp e he A B _ _ hAB hAB1 hConn hConn1'
  refine ⟨A0, u, fun ρ => (hAB0 ρ).1, hu, fun ρ => ?_, hcurv, hhol, hA⟩
  exact ((hAB1 ρ).1.sub (hAB0 ρ).1).congr (fun ζ _ => by ring)

def GTCHolOfCut : Prop := GTCRef → GTCPhaseRel → GTCConnUniq → GTCConnPhase → GTCPhHol → GTCHol

theorem gTCHol_of_cut : GTCHolOfCut := by
  intro hRef hPR hU hCP hPh Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR
  obtain ⟨A0, u, hA0s, hu, hws, -, hhol, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  obtain ⟨n1, hn1⟩ := hhol ρ R hR0 hR
  obtain ⟨n2, hn2⟩ := hPh P.TT (u ρ) (hu ρ).1 (hu ρ).2 R hR0 hR
  have hsph := sphere_sub_ann P hR0 hR
  have hf : CircleIntegrable (fun w => modA P ρ w - A0 ρ w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le (((modA_smooth P ρ hTT).sub (hA0s ρ)).continuousOn.mono hsph)
  have hg : CircleIntegrable (fun w => star (u ρ w) * NF.dZ (u ρ) w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le ((hws ρ).continuousOn.mono hsph)
  have heq : (∮ w in C(0, R), modA P ρ w - A ρ w) =
      ∮ w in C(0, R), (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    apply circleIntegral.integral_congr hR0.le
    intro w hw
    try dsimp only
    rw [hA ρ w (hsph hw)]
    ring
  refine ⟨n1 - n2, ?_⟩
  rw [heq, circleIntegral.integral_sub hf hg, Complex.sub_im, hn1, hn2]
  push_cast
  ring

def GTCCurvOfCut : Prop := GTCRef → GTCPhaseRel → GTCConnUniq → GTCConnPhase → GTCPhCurv → GTCCurv

theorem gTCCurv_of_cut : GTCCurvOfCut := by
  intro hRef hPR hU hCP hPc Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
  obtain ⟨A0, u, hA0s, hu, hws, hcurv, -, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  have hnhds : Ann P ∈ nhds ζ := (ann_isOpen P).mem_nhds hζ
  have hev : (fun w => modA P ρ w - A ρ w) =ᶠ[nhds ζ]
      fun w => (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    filter_upwards [hnhds] with w hw
    rw [hA ρ w hw]
    ring
  have hfd : DifferentiableAt ℝ (fun w => modA P ρ w - A0 ρ w) ζ :=
    (((modA_smooth P ρ hTT).sub (hA0s ρ)).differentiableOn (by simp)).differentiableAt hnhds
  have hgd : DifferentiableAt ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ :=
    ((hws ρ).differentiableOn (by simp)).differentiableAt hnhds
  have hder : fderiv ℝ (fun w => modA P ρ w - A ρ w) ζ =
      fderiv ℝ (fun w => modA P ρ w - A0 ρ w) ζ - fderiv ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ := by
    exact hev.fderiv_eq.trans (hfd.hasFDerivAt.sub hgd.hasFDerivAt).fderiv
  have h1 := hcurv ρ ζ hζ
  have h2 := hPc P.TT (u ρ) (hu ρ).1 (hu ρ).2 ζ hζ
  unfold NF.dZb at h1 h2 ⊢
  rw [hder, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  have key : ∀ a b c d : ℂ, (1 / 2 : ℂ) * ((a - b) + Complex.I * (c - d)) =
      (1 / 2 : ℂ) * (a + Complex.I * c) - (1 / 2 : ℂ) * (b + Complex.I * d) := by
    intros; ring
  rw [key, Complex.sub_re, h1, h2, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
