import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

namespace Formalism.FourierDecayAlt.P.TBBx3

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecCutAt_of_one (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hχ : ∀ x, 1 ≤ x → χ x = 1) : TBB.VecCutAt p χ F := by
  intro ε hε γ hγ hle
  have hle0 : ε ≤ D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hle
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF]
    have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose hγ h'.choose_spec.2.1
    have hle' : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hle0
    rw [hχ _ ((one_le_div hε).mpr hle'), Complex.ofReal_one, one_smul]
  · rfl
  · rfl

theorem hsInner_self_re_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ (B.hsInner A A).re := by
  unfold B.hsInner
  have h := inner_self_nonneg (𝕜 := ℂ) (x := B.hsVec A)
  simpa using h

theorem rr_top_re_nonneg (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter)
    (h : C.LPt) (hi : P.r < i) : 0 ≤ (p.RR F i w h h).re := by
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt h i ∧ D.IsLocPt h i
  · rw [dif_pos h1, dif_neg (by omega)]
    by_cases h2 : i = P.r + 1
    · rw [if_pos h2]
      by_cases h3 : w = []
      · rw [if_pos h3]
        exact hsInner_self_re_nonneg _
      · rw [if_neg h3]
        unfold Top.topOf
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun e _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun ρ _ => ?_
        rw [Complex.re_ofReal_mul]
        exact mul_nonneg (mul_self_nonneg _) (hsInner_self_re_nonneg _)
    · rw [if_neg h2]
      simp
  · rw [dif_neg h1]
    simp

theorem posAt_of_forms (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hnn : ∀ y, 0 ≤ nn y)
    (hform : ∀ (j : ℕ) (w : List C.Letter) (h : C.LPt), j ≤ P.r → TBB.AdmW P p.l0 Y w → w.length ≤ N →
      0 ≤ (p.RR F j w h h).re) : TBB.PosAt p nn F Y N := by
  intro i w h hw hN
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul]
  apply mul_nonneg
  · apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    unfold TBB.normC
    apply List.prod_nonneg
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨l, _, rfl⟩ := ha
    exact hnn _
  · by_cases hi : i ≤ P.r
    · exact hform i w h hi hw hN
    · exact rr_top_re_nonneg p F i w h (by omega)

theorem head_continuity_at_zero_of_standard (hPS : KB.PStd) (hTP : P5.ThmPActual) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) : TBB.HeadContinuityAtZero p nn F Y N := by
  intro j hj h hh w hw hN
  obtain ⟨φ, hφc, hφi, hφ, -⟩ := hPS hTP Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  refine ⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩
  intro c hc
  simp only
  rw [hφ c hc]
  have hA : 0 ≤ A := Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

theorem ew_zero_nil (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    TBB.Ew p nn G 0 w [] = (p.RR G 0 w [] []).re / TBB.normC nn w := by
  have h1 : ∀ TT : ℝ, TBB.nPt P.k P.r TT [] = 1 := fun TT => by simp [TBB.nPt, C.nAux]
  unfold TBB.Ew TBB.NP
  simp only [h1, Real.sqrt_one, one_mul]
  rw [Complex.re_ofReal_mul, one_div, inv_mul_eq_div]

theorem limZeroAt_of_limits (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F) :
    TBB.LimZeroAt p nn χ F Y N κ₀ := by
  intro w hw hN
  obtain ⟨sz, hsz0, hszn, hlim⟩ := hE w hw hN
  have hEw : ∀ ε, TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re / TBB.normC nn w := fun ε => ew_zero_nil p nn _ w
  have hlim2 : Tendsto (fun ε => ENNReal.ofReal (TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [])) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (sz * (B.beta p.T.base F F).re / TBB.normC nn w))) := by
    simp only [hEw]
    exact ENNReal.tendsto_ofReal (hlim.div_const _)
  rw [hlim2.limsup_eq]
  refine le_trans ?_ hB
  rw [ENNReal.ofReal_le_ofReal_iff']
  have hn0 : 0 ≤ TBB.normC nn w := le_trans hsz0 hszn
  by_cases hb : 0 ≤ (B.beta p.T.base F F).re
  · left
    rcases hn0.lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]
      calc sz * (B.beta p.T.base F F).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re :=
            mul_le_mul_of_nonneg_right hszn hb
        _ = (B.beta p.T.base F F).re * TBB.normC nn w := mul_comm _ _
    · rw [← hzero, div_zero]
      exact hb
  · right
    push_neg at hb
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hsz0 hb.le) hn0

end

end Formalism.FourierDecayAlt.P.TBBx3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem vector_truncation_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hχ : ∀ x, 1 ≤ x → χ x = 1) : Formalism.FourierDecayAlt.TBB.VecCutAt p χ F := by
  exact TBBx3.vecCutAt_of_one p χ F hχ

theorem head_continuity_at_zero_of_compact_coefficients (hPS : KB.PStd) (hTP : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) :
    Formalism.FourierDecayAlt.TBB.HeadContinuityAtZero p nn F Y N := by
  exact TBBx3.head_continuity_at_zero_of_standard hPS hTP p nn F Y N Cb hCb hF

theorem limit_zero_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, Formalism.FourierDecayAlt.TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ Formalism.FourierDecayAlt.TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * Formalism.FourierDecayAlt.TBB.jN2 p F) :
    Formalism.FourierDecayAlt.TBB.LimZeroAt p nn χ F Y N κ₀ := by
  exact TBBx3.limZeroAt_of_limits p nn χ F Y N κ₀ hE hB

end Formalism.FourierDecayAlt.P
