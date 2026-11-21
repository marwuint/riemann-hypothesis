import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubProdLeSumOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeDefectLeOfDividedWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SevenMulHeightBoundLeHalfOfParameters

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.ZedSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem bar_gap (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (hi : (i : ℕ) + 1 < D.R.m) (τ : Psi p.T.Q.H)
    (a b : Fin ((dat p i).p + (dat p i).q)) (hab : (b : ℕ) = a + 1) (hb : (b : ℕ) = (dat p i).p) :
    LevelStarExponents.h0 L ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
  obtain ⟨t, ht⟩ := WtShape.exists_tau p τ
  have e1 := WtShape.dat_p p i
  have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) = WtShape.sgR D t a - WtShape.sgR D t (a + 1) - 1 +
      if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
    rw [Int.cast_sub, WtShape.uW_real p i τ t ht, WtShape.uW_real p i τ t ht, hab, ← WtShape.entR_step]; ring
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have h1 := WtShape.sgR_step_low D L P t a (by omega) (by omega)
  rw [if_pos (by omega)] at hd
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast WtShape.six_le_r D.R
  linarith

abbrev wp (p : PtAt ex Csz) (i : Fin D.R.m) (PP : ℝ) : WtPar (dat p i) :=
  ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩

theorem zed_at (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (T : ParamsT D L P) (A M C1 : ℝ)
    (hS : SizeAt p i T.PP C1) (hq : ∀ u1, Quo p i T.PP u1 → u1 = (wp p i T.PP).u₁)
    (hsa : ∀ τ, StrictAnti ((wp p i T.PP).u₁ τ)) (hH : HostNum D L T.PP A M) (hW : WtNum p i T.PP)
    (hi : (i : ℕ) + 1 < D.R.m) :
    zed p i T.PP (wp p i T.PP).u₁ * (T.PP * kap p i) ≤ L.sc.b / 2 := by
  obtain ⟨hb1, -, -, -, -, hbk, hquo⟩ := hS
  obtain ⟨u0, hu0⟩ := (hquo hi).1
  have hQ : Quo p i T.PP (wp p i T.PP).u₁ := hq u0 hu0 ▸ hu0
  obtain ⟨h0', S, eta, -, -, -, -, -, hHyp⟩ := hW.hyp hi
  have hDv : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).IsDiv := (quo_iff p i T.PP h0' S eta _).1 hQ
  have hY : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).Hyp := hHyp _
  have hDp : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := hW.dim.trans T.Dp_eq.symm
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hDp]; exact Nat.ceil_le.2 (WtShape.len_le D L P T)
  obtain ⟨s1, s2, -⟩ := WtShape.spacing_ge T ((i : ℕ) + 1) _ hlen
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  have hb0 : 0 < L.sc.b := by linarith
  have hsb : 0 < Real.sqrt L.sc.b := Real.sqrt_pos.2 hb0
  have hw : ∀ τ, Real.sqrt L.sc.b / 2 ≤ (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) := fun τ => by
    have := hW.low τ; have := hH.low; linarith
  have hrho := _root_.GlobalTheory.MeanTop.rho_div_le _ _ (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁) (LevelStarExponents.h0 L) hY hDv hsa
    (fun τ => lt_of_lt_of_le (by positivity) (hw τ))
    (by
      show 4 * (((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) + (lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1) ≤ LevelStarExponents.h0 L
      rw [eN, hDp]; simpa [cZero] using s1)
    (by
      show 24 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) ≤ LevelStarExponents.h0 L
      rw [eN]; exact s2)
    (fun τ a b hab hb => bar_gap p i P hi τ a b hab hb)
  have hrB : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ = GlobalTheory.CompHt.rhoOf (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u'
      (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u1 := by
    unfold GlobalTheory.CompHt.rhoB; congr 1; funext τ j; rw [GlobalTheory.CompHt.uPrime_apply]; rfl
  have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← Nat.card_eq_fintype_card, hW.card]
  have hrho' : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ ≤ 3 * (D.R.r : ℝ) * ((D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) * (2 / Real.sqrt L.sc.b))) := by
    rw [hrB]
    refine hrho.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_card_nsmul _ _ ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) *
      (2 / Real.sqrt L.sc.b)) fun τ _ => ?_) (by rw [eN]; positivity)).trans_eq ?_)
    · show (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          (2 * ((lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1)) / LevelStarExponents.h0 L +
          2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) /
          (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ _
      rw [eN, hDp]
      have hwp : 0 < (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) :=
        lt_of_lt_of_le (by positivity) (hw τ)
      have h2 : 1 / (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 2 / Real.sqrt L.sc.b := by
        rw [div_le_div_iff₀ hwp hsb]; linarith [hw τ]
      have h3 : 0 ≤ 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) := by positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      rw [mul_one_div] at h4
      linarith
    · rw [Finset.card_univ, nsmul_eq_mul, hcard, eN]
  have hk : kap p i ≤ 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
    show ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ _
    calc ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|
        ≤ ∑ τ : Psi p.T.Q.H, ∑ k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b := by
          gcongr with τ _ k _; exact hW.up τ k
      _ = 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hcard, eN]; ring
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have h8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
    linarith
  have hD1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast WtShape.one_le_Dp T
  have hTl : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ (lenT p i T.PP : ℝ) := by
    unfold lenT; rw [hDp]; exact Nat.le_ceil _
  have hTO : (lenT p i T.PP : ℝ) ≤ T.TO := by exact_mod_cast hlen
  have hT4 : 4 * (T.Dp : ℝ) + 4 ≤ lenT p i T.PP := by
    have := hY.h1
    have h : 4 * T.Dp + 4 ≤ lenT p i T.PP := by rw [← hDp]; exact this
    exact_mod_cast h
  have hH0 : (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP ≤ LevelStarExponents.h0 L := by
    refine le_trans ?_ T.heightBound_ge_order_product
    have hP : 0 ≤ T.PP := by linarith [WtShape.forty_le_PP T]
    have : 0 ≤ (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP := by positivity
    nlinarith [T.ChT_ge]
  have hn0 : 2500 * (D.R.r : ℝ) * ((T.Dp : ℝ) + 1) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have h' : 2500 * D.R.r * (T.Dp + 1) ≤ T.TO := le_trans (by
      rw [show 2500 * D.R.r * (T.Dp + 1) = 2 * (2 * 5 ^ 4 * D.R.r) * (T.Dp + 1) by ring]; exact Nat.le_add_left _ _) h
    exact_mod_cast h'
  have hnW : (D.R.f : ℝ) * D.R.r * ((D.R.r : ℝ) + 1) ≤ T.nWn := by exact_mod_cast T.nW_lo.1
  have hP3 : T.PP ^ 3 * (T.TO : ℝ) ^ 2 ≤ Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; exact T.precision_cube_order_sq_le_sqrt
  have hsp : (T.TO : ℝ) * T.nWn ≤ D.R.r + D.R.t := by
    have h := T.split
    have h' : T.TO * T.nWn ≤ D.R.r + D.R.t := by omega
    exact_mod_cast h'
  have hNb : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ D.R.N D.R.m := by
    have h' : D.R.m * (D.R.t + 1) ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast h'
  have key := _root_.GlobalTheory.seven_mul_height_bound_le_half (T.Dp : ℝ) (lenT p i T.PP : ℝ) (GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁) T.PP (kap p i) L.sc.b
    D.R.f D.R.r D.R.m D.R.k (LevelStarExponents.h0 L) T.TO (D.R.N D.R.m) T.nWn D.R.t hD1 hb0 hf1 hm2 hmk (WtShape.r_cast D.R)
    (Nat.cast_nonneg _) (sizeK_nonneg _ _ _) hk hTl hTO hT4 hrho' hH0 hn0 hnW T.PP_nW hP3 hsp hNb
  unfold zed
  rw [hDp]
  exact key

end GlobalTheory.CovTop.ZedSz
