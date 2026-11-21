import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaWeightedNorm
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CfwMOfExtraBounds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BasePsiLeviLowerBound

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
open GlobalTheory.FrameThetaCompare (transfer curv_lin diagForm chart_smooth smooth_of_chart mem_SS_iff lower_iff
  upper_iff bdd_of_upper curvDe_eq_omRh curvDe_nonneg card_pos)

namespace GlobalTheory.ThetaRecordCompare

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem levi_eq (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : levi X x0 u z ξ = leviM X u x0 z ξ := rfl

theorem levi_rh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    levi X x0 (rh X) z ξ = leviRh X x0 z ξ := rfl

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma twoDelta_sub_eq_two_mul_blockWt_sub {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {de : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X de) (τ : X.Ψ) (a b : Fin r) :
    ((de τ a : ℤ) : ℝ) - ((de τ b : ℤ) : ℝ) =
      2 * (((_root_.GlobalTheory.CurvMargin.blockWt X τ a : ℤ) : ℝ) -
        ((_root_.GlobalTheory.CurvMargin.blockWt X τ b : ℤ) : ℝ)) := by
  have key : de τ a - de τ b =
      2 * (_root_.GlobalTheory.CurvMargin.blockWt X τ a - _root_.GlobalTheory.CurvMargin.blockWt X τ b) := by
    by_cases ha : (a : ℕ) < X.p0 <;> by_cases hb : (b : ℕ) < X.p0
    · have := (h τ a b).1 (iff_of_true ha hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ a b).2 ha (not_lt.1 hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ b a).2 hb (not_lt.1 ha)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ a b).1 (iff_of_false ha hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
  exact_mod_cast key

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.ThetaRecordCompare.levi_twoDelta {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {de : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X de) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) {z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)} (hz : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0)
    (ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.levi X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X de) z ξ = 2 * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviRh X x0 z ξ := by
  rw [_root_.GlobalTheory.CurvMargin.leviRh_eq X x0 ho hz ξ]
  obtain ⟨x1, D, -, -, -, hdiag, -⟩ := _root_.GlobalTheory.FrameThetaCompare.transfer X x0 z hz
  change _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 de z ξ =
    2 * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 (_root_.GlobalTheory.CurvMargin.blockWt X) z ξ
  rw [hdiag, hdiag]
  unfold _root_.GlobalTheory.FrameThetaCompare.diagForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [twoDelta_sub_eq_two_mul_blockWt_sub h]
  ring

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThetaRecordCompare.leviRh_nonneg (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) {z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)}
    (hz : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0) (ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviRh X x0 z ξ := by
  have h0 := _root_.GlobalTheory.FrameThetaCompare.curvDe_nonneg X (x0 := x0) hz ξ
  rw [_root_.GlobalTheory.FrameThetaCompare.curvDe_eq_omRh X ho hz ξ] at h0
  exact h0

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThetaRecordCompare.gapsGe_mono {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {g g' : ℝ}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la g) (hg : g' ≤ g) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la g' :=
  fun τ i j hij hne => hg.trans (h τ i j hij hne)

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.ThetaRecordCompare.cusp_of_gaps {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} (hn : 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)
    (h0 : 0 < X.p0) (hr : X.p0 < r) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (hg : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la 0) (hp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la 1) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) :
    P ∈ X.SS la := by
  obtain ⟨τ0, hτ0⟩ := Finset.card_pos.1 (_root_.GlobalTheory.FrameThetaCompare.card_pos hn)
  have key := @_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.cuspStatement_holds E _ _ _
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.CuspStatement at key
  refine key r X la ⟨τ0, hτ0⟩ h0 hr (fun i j hij hne => ?_) (fun i0 i1 hi0 hi1 => ?_) P hP
  · have h1 : (0 : ℤ) ≤ la ⟨τ0, hτ0⟩ i - la ⟨τ0, hτ0⟩ j := by exact_mod_cast hg _ i j hij hne
    omega
  · have h1 : (1 : ℤ) ≤ la ⟨τ0, hτ0⟩ i1 - la ⟨τ0, hτ0⟩ i0 := by
      exact_mod_cast hp _ i0 i1 hi0 hi1
    omega

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThetaRecordCompare.two_le_r {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} (hn : 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) : 2 ≤ r := by
  by_contra hlt
  push_neg at hlt
  have hempty : IsEmpty (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent
    refine ⟨fun ⟨_, ⟨p, hp⟩⟩ => ?_⟩
    have h1 := p.1.isLt
    have h2 : (p.2 : ℕ) < p.1 := hp
    omega
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd at hn
  rw [Fintype.card_eq_zero_iff.2 hempty] at hn
  omega

section Records

variable {X : Data E r}

theorem T_pos {T : ℕ} (hn : 2 ≤ nd X) (hT : 11 * nd X ^ 2 ≤ T) : (0 : ℝ) < T := by
  have : 0 < T := lt_of_lt_of_le (by positivity) hT
  exact_mod_cast this

theorem w_nz (I : ThetaIn X) (x : Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ k, I.w k x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := I.w_lower
  have := (Real.exp_pos _).trans_le (hC x hx)
  simp [wnorm, Data.pnorm, h] at this

theorem frame_theta_const_pos (I : ThetaIn X) : 0 < I.c1 := by
  have h1 := T_pos I.two_le_D I.T_ge
  have h2 := I.c_pos
  have h3 : 0 < I.RR := one_pos.trans_le I.one_le_RR
  have h4 := I.dp_pos
  have h5 := I.qp_pos
  unfold ThetaIn.c1
  positivity

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma cpt_zero_jet_harmonics (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 = x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.mat]
  funext τ a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp only [Matrix.of_apply]
    split_ifs <;> first | exact mul_zero _ | simp_all
  · simp

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma exists_surjective_diagForm_leviM (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) :
    ∃ x0 ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 ∈ X.dom ∧
      ∃ D : (Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) →ₗ[ℂ] Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ, Function.Surjective D ∧
        ∀ la ξ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviM X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la) x0 0 ξ = _root_.GlobalTheory.FrameThetaCompare.diagForm X la (D ξ) := by
  obtain ⟨x0, hx0, -⟩ := A.et_ne
  have hd : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 ∈ X.dom := by rw [cpt_zero_jet_harmonics]; exact hx0
  obtain ⟨x1, D, -, hD, -, hdiag, -⟩ := _root_.GlobalTheory.FrameThetaCompare.transfer X x0 0 hd
  exact ⟨x0, hx0, hd, D, LinearMap.injective_iff_surjective.1 hD, fun la ξ => hdiag la ξ⟩

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma diagForm_L_pos (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) {η : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ} (hη : η ≠ 0) :
    0 < _root_.GlobalTheory.FrameThetaCompare.diagForm X A.L η := by
  obtain ⟨x0, hx0, hd, D, hD, hdiag⟩ := exists_surjective_diagForm_leviM A
  obtain ⟨ξ, rfl⟩ := hD η
  have hξ : ξ ≠ 0 := by rintro rfl; exact hη (map_zero D)
  rw [← hdiag]
  exact A.posL x0 hx0 0 hd ξ hξ

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma single_ne_zero_jet_harmonics (τ : X.Ψ) (i j : Fin r) (h : i < j) :
    (fun k : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) =>
      if (k : ℕ) = (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) then (1 : ℂ) else 0 :
      Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) ≠ 0 := fun hz => by
  have := congrFun hz (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩))
  simp only [if_pos rfl] at this
  exact one_ne_zero this

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma diagForm_single' (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (τ : X.Ψ) (i j : Fin r) (h : i < j) :
    _root_.GlobalTheory.FrameThetaCompare.diagForm X la
        (fun k : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) =>
          if (k : ℕ) = (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) then 1 else 0) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i * (((la τ i : ℤ) : ℝ) - ((la τ j : ℤ) : ℝ)) := by
  unfold _root_.GlobalTheory.FrameThetaCompare.diagForm
  rw [Finset.sum_eq_single (τ, ⟨(j, i), h⟩)]
  · simp
  · intro e _ he
    have hne : ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) e : Fin _) : ℕ) ≠
        (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) := fun h' =>
      he ((Fintype.equivFin _).injective (Fin.ext h'))
    simp only [hne, if_false]
    simp
  · simp

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma diagForm_Fp_sub_pos (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) {η : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ} (hη : η ≠ 0) :
    0 < _root_.GlobalTheory.FrameThetaCompare.diagForm X (A.Fp - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X • A.L) η := by
  obtain ⟨x0, hx0, hd, D, hD, hdiag⟩ := exists_surjective_diagForm_leviM A
  obtain ⟨ξ, rfl⟩ := hD η
  have hξ : ξ ≠ 0 := by rintro rfl; exact hη (map_zero D)
  obtain ⟨c, hc, hF⟩ := A.posF
  have h1 := A.posL x0 hx0 0 hd ξ hξ
  have h2 := hF 0 le_rfl (by rw [zero_mul]; positivity) x0 hx0 0 hd ξ
  rw [← hdiag]
  have h3 := mul_pos (mul_pos two_pos hc) h1
  linarith

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.ThetaRecordCompare.arch_gaps (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) (h0 : 0 < X.p0)
    (hr : X.p0 < r) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X A.L 1 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X A.L 1 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X A.Fp 0 ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X A.Fp 1 := by
  have hn : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) := by exact_mod_cast A.n_ge
  have gL : ∀ (τ : X.Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 →
      1 ≤ A.L τ i - A.L τ j := by
    intro τ i j hij hne
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i = 1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      by_cases hj : (j : ℕ) < X.p0
      · rw [if_pos hj, if_pos (by omega)]; norm_num
      · rw [if_neg hj, if_neg (by omega)]; norm_num
    have h1 := diagForm_L_pos A (single_ne_zero_jet_harmonics τ i j hlt)
    rw [diagForm_single' A.L τ i j hlt, hs, one_mul] at h1
    have h2 : (0 : ℤ) < A.L τ i - A.L τ j := by
      exact_mod_cast (by linarith : (0 : ℝ) < ((A.L τ i : ℤ) : ℝ) - ((A.L τ j : ℤ) : ℝ))
    omega
  have pL : ∀ (τ : X.Ψ) (i0 i1 : Fin r), (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 →
      1 ≤ A.L τ i1 - A.L τ i0 := by
    intro τ i0 i1 hi0 hi1
    have hlt : i0 < i1 := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i0 = -1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      rw [if_neg (by omega), if_pos (by omega)]; norm_num
    have h1 := diagForm_L_pos A (single_ne_zero_jet_harmonics τ i0 i1 hlt)
    rw [diagForm_single' A.L τ i0 i1 hlt, hs] at h1
    have h2 : (0 : ℤ) < A.L τ i1 - A.L τ i0 := by
      exact_mod_cast (by linarith : (0 : ℝ) < ((A.L τ i1 : ℤ) : ℝ) - ((A.L τ i0 : ℤ) : ℝ))
    omega
  refine ⟨fun τ i j hij hne => by exact_mod_cast gL τ i j hij hne,
    fun τ i0 i1 hi0 hi1 => by exact_mod_cast pL τ i0 i1 hi0 hi1, ?_, ?_⟩
  · intro τ i j hij hne
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i = 1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      by_cases hj : (j : ℕ) < X.p0
      · rw [if_pos hj, if_pos (by omega)]; norm_num
      · rw [if_neg hj, if_neg (by omega)]; norm_num
    have h1 := diagForm_Fp_sub_pos A (single_ne_zero_jet_harmonics τ i j hlt)
    rw [diagForm_single' _ τ i j hlt, hs, one_mul] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW] at h1
    push_cast at h1
    have hR : (0 : ℝ) < ((A.Fp τ i - A.Fp τ j + 2 * ((j : ℤ) - i) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) : ℤ) : ℝ) := by
      push_cast; linarith
    have hZ : (0 : ℤ) < A.Fp τ i - A.Fp τ j + 2 * ((j : ℤ) - i) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) := by exact_mod_cast hR
    have hg := gL τ i j hij hne
    have hji : (j : ℤ) - i = 1 := by omega
    have hm : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) := by nlinarith
    have : (0 : ℤ) ≤ A.Fp τ i - A.Fp τ j := by linarith
    exact_mod_cast this
  · intro τ i0 i1 hi0 hi1
    have hlt : i0 < i1 := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i0 = -1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      rw [if_neg (by omega), if_pos (by omega)]; norm_num
    have h1 := diagForm_Fp_sub_pos A (single_ne_zero_jet_harmonics τ i0 i1 hlt)
    rw [diagForm_single' _ τ i0 i1 hlt, hs] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW] at h1
    push_cast at h1
    have hR : (0 : ℝ) < ((A.Fp τ i1 - A.Fp τ i0 - 2 * ((i1 : ℤ) - i0) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) : ℤ) : ℝ) := by
      push_cast; linarith
    have hZ : (0 : ℤ) < A.Fp τ i1 - A.Fp τ i0 - 2 * ((i1 : ℤ) - i0) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) := by exact_mod_cast hR
    have hg := pL τ i0 i1 hi0 hi1
    have hji : (0 : ℤ) ≤ (i1 : ℤ) - i0 := by omega
    have hm : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) := by nlinarith
    have : (1 : ℤ) ≤ A.Fp τ i1 - A.Fp τ i0 := by linarith
    exact_mod_cast this

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.ThetaRecordCompare.arch_extra (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsExtra X A.ps0 A.a1 := by
  have hinv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsInv X A.ps0 :=
    (_root_.GlobalTheory.FrameThetaCompare.isInv_iff X _).2 A.potential_invariant
  refine ⟨A.frame_theta_weight_pos.le, hinv, ?_, ?_, ?_⟩
  · exact _root_.GlobalTheory.FrameThetaCompare.smooth_of_chart X hinv.1 A.potential_smooth
  · obtain ⟨B, hB⟩ := _root_.GlobalTheory.FlatCompare.bdd_add_log X A.base_psi_weighted_cf A.frame_theta_weight_pos 0
    exact ⟨B, fun x hx => by simpa using hB x hx⟩
  · obtain ⟨A', hdec, C, hC⟩ := (_root_.GlobalTheory.FlatCompare.extraBounds_iff X A.ps0 A.frame_theta_weight_pos.le).2 A.base_psi_weighted_cf
    exact ⟨A', ⟨C, hC⟩, fun η hη => hdec η hη⟩

def Agree (I : ThetaIn X) (A : ArchInM X) : Prop :=
  A.L = I.L ∧ A.de = I.de2 ∧ A.Fp = I.Fp ∧ A.T = I.T ∧ A.i = I.i ∧
    A.g0 = I.g0 ∧ A.c = I.c ∧ A.c1 = I.c1 ∧ A.a1 = I.a1 ∧ A.rr = r ∧
    (⟨A.N, A.w⟩ : Σ N : ℕ, Fin N → Frame X.Ψ r → ℂ) = ⟨I.N, I.w⟩ ∧
    A.ph = I.ph ∧ A.et = I.et ∧ A.th1 = I.th1 ∧ A.th2 = I.th2 ∧ A.thp = I.thp ∧ A.ps0 = I.ps0

theorem Agree.unique {I : ThetaIn X} {A A' : ArchInM X} (h : Agree I A) (h' : Agree I A') :
    A = A' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17⟩ := h'
  have e11 := h11.trans k11.symm
  cases A; cases A'
  dsimp only at *
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13 h14 h15 h16 h17
  subst k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k12 k13 k14 k15 k16 k17
  cases e11
  rfl

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.ThetaRecordCompare.gaps_add {la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la 0)
    (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la' 0) (k : ℕ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X (la + k • la') 0 := by
  intro τ i j hij hne
  have a1 : (0 : ℤ) ≤ la τ i - la τ j := by exact_mod_cast h τ i j hij hne
  have a2 : (0 : ℤ) ≤ la' τ i - la' τ j := by exact_mod_cast h' τ i j hij hne
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have : (0 : ℤ) ≤ (la + k • la') τ i - (la + k • la') τ j := by
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    nlinarith
  exact_mod_cast this

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.ThetaRecordCompare.pair_add {la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la 1)
    (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la' 1) (k : ℕ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X (la + k • la') 1 := by
  intro τ i0 i1 hi0 hi1
  have a1 : (1 : ℤ) ≤ la τ i1 - la τ i0 := by exact_mod_cast h τ i0 i1 hi0 hi1
  have a2 : (1 : ℤ) ≤ la' τ i1 - la' τ i0 := by exact_mod_cast h' τ i0 i1 hi0 hi1
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have : (1 : ℤ) ≤ (la + k • la') τ i1 - (la + k • la') τ i0 := by
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    nlinarith
  exact_mod_cast this

end Records

end

end GlobalTheory.ThetaRecordCompare
