import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModels
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundJoin
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesDefiniteLiftIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem archOne_congr {X X' : Data E r} (hX : X = X') {L Fp : Wt X.Ψ r} {L' Fp' : Wt X'.Ψ r} {T : ℕ}
    (hL : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, L ⟨τ, h1⟩ a = L' ⟨τ, h2⟩ a)
    (hF : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, Fp ⟨τ, h1⟩ a = Fp' ⟨τ, h2⟩ a) (h : ArchOne X' L' Fp' T) :
    ArchOne X L Fp T := by
  subst hX
  have e1 : L = L' := funext fun τ => funext fun a => hL τ.1 τ.2 τ.2 a
  have e2 : Fp = Fp' := funext fun τ => funext fun a => hF τ.1 τ.2 τ.2 a
  subst e1 e2
  exact h

theorem archOn_of_comps {U C K : Type} [Group U] [MulAction U C] [Nonempty C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r)
    (X : K → Data E r) (e : C ≃ K) (hX : ∀ c, (M.comp c).toData = X (e c)) (lK lL lF : ∀ k, Wt (X k).Ψ r) (T n : ℕ)
    (hn : n = M.dimY)
    (hka : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = lK (e c) ⟨τ, h2⟩ a)
    (hsum : ∀ k, lK k = lF k + T • lL k)
    (hLi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lL k ⟨τ, h⟩ a = lL k' ⟨τ, h'⟩ a)
    (hFi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lF k ⟨τ, h⟩ a = lF k' ⟨τ, h'⟩ a)
    (hW : ∀ k, GapsGe (X k).p0 (lL k) 1 ∧ PairGe (lL k) (1.9 * T) ∧
      GapsGe (X k).p0 (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 0 ∧ PairGe (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 1)
    (hA : ∀ k, ArchOne (X k) (lL k) (lF k) T) : ArchOn M ka T := by
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hΨ : ∀ c, (X (e c)).Ψ = M.Ψ := fun c => (congrArg Data.Ψ (hX c)).symm.trans (M.comp_Ψ c)
  have hp : ∀ c, (X (e c)).p0 = M.p0 := fun c => (congrArg Data.p0 (hX c)).symm.trans (M.comp_basePoint c)
  have mem : ∀ c τ, τ ∈ M.Ψ → τ ∈ (X (e c)).Ψ := fun c τ h => (hΨ c).symm ▸ h
  let L : Wt M.Ψ r := fun τ a => lL (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  let Fp : Wt M.Ψ r := fun τ a => lF (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  have hW0 := hW (e c0)
  rw [hp c0, hn] at hW0
  obtain ⟨w1, w2, w3, w4⟩ := hW0
  refine ⟨L, Fp, ?_, fun τ a b h1 h2 => w1 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w2 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun τ a b h1 h2 => w3 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w4 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun c => ?_⟩
  · funext τ a
    rw [hka c0 τ.1 τ.2 (mem c0 τ.1 τ.2) a, hsum]
    rfl
  · refine archOne_congr (hX c) (fun τ h1 h2 a => ?_) (fun τ h1 h2 a => ?_) (hA (e c))
    · exact hLi (e c0) (e c) τ _ h2 a
    · exact hFi (e c0) (e c) τ _ h2 a

end Model

section Run

theorem row_pair {r p q : ℕ} (hpq : p + q = r) (Dm nL nF : ℤ) (hnF : 0 ≤ nF)
    (LP LM FP FM : ℕ → ℤ) (L F : Fin r → ℤ)
    (hL : ∀ a : Fin r, L a = if q ≤ (a : ℕ) then LP (a - q) + nL else -LM (q - 1 - a) - nL)
    (hF : ∀ a : Fin r, F a = if q ≤ (a : ℕ) then FP (a - q) + nF else -FM (q - 1 - a) - nF)
    (p4 : (Dm + 2) * LP (p - 1) + ((Dm + 2) * (2 * nL) + 2 * r) ≤ FP (p - 1))
    (m4 : (Dm + 2) * LM (q - 1) + 0 ≤ FM (q - 1)) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) = r - 1)
    (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (F b - (2 * (b : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L b) -
      (F a - (2 * (a : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L a) := by
  have hq1 : q ≤ (b : ℕ) := by omega
  have hq2 : ¬ q ≤ (a : ℕ) := by omega
  have e1 : (a : ℤ) = 0 := by omega
  have e2 : (b : ℤ) = r - 1 := by omega
  have e3 : (r : ℤ) = p + q := by omega
  rw [hL a, hL b, hF a, hF b, e1, e2]
  simp only [if_pos hq1, if_neg hq2]
  rw [show (b : ℕ) - q = p - 1 by omega, show q - 1 - (a : ℕ) = q - 1 by omega]
  nlinarith

theorem expand_weight {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)} (F L : Wt Ψ r)
    (n : ℕ) (τ : Ψ) (c : Fin r) :
    (F - kLog Ψ r - (n + 2) • L) τ c = F τ c - (2 * (c : ℤ) - ((r : ℤ) - 1)) - ((n : ℤ) + 2) * L τ c := by
  show F τ c - kLog Ψ r τ c - ((n + 2) • L τ c) = _
  rw [nsmul_eq_mul]
  simp only [kLog]
  push_cast
  ring

set_option maxHeartbeats 1000000 in

theorem run_weight_arch (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (hP : FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0) (hjm : j < D.R.m)
    (k : (T.U j T.σ₀).Comp) :
    GapsGe ((T.U j T.σ₀).X k).p0 (laR T j wL k) 1 ∧ PairGe (laR T j wL k) (1.9 * Tn) ∧
      GapsGe ((T.U j T.σ₀).X k).p0
        (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 0 ∧
      PairGe (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 1 := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, g1, g2, h4, -, h6, h7, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, h21, -⟩ := hS
  obtain ⟨-, -, -, -, -, hp0, -, tt, hla⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  have hk := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have hq : 0 < (D.R.sigW j).2 := by show 0 < D.R.m - j; omega
  have hpq : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
    show D.R.k + j - 1 + (D.R.m - j) = D.R.k + D.R.m - 1; omega
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by unfold Tp; push_cast; ring
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40
  have h21' : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ Tn := by exact_mod_cast h21
  have hn : (nW : ℤ) = 2 * ((wL.n / 2 : ℕ) : ℤ) := by
    have := hL.1
    obtain ⟨c, hc⟩ := wL.n_even
    omega
  have key := fun τ : ((T.U j T.σ₀).X k).Ψ => by
    have bP := GlobalTheory.RunWeightDom.block hp (ka.aP (tt τ)) (wL.aP (tt τ)) (wF.aP (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' h21'
      (fun i hi => by have := g1 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP (tt τ) i : ℝ) := by have := h6 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.1 (tt τ) i; rwa [hTp, sub_sub] at this) (hF.2.1 (tt τ))
    have bM := GlobalTheory.RunWeightDom.block hq (ka.aM (tt τ)) (wL.aM (tt τ)) (wF.aM (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      0 (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' (Int.natCast_nonneg _)
      (fun i hi => by have := g2 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aM (tt τ) i : ℝ) := by have := h7 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.2 (tt τ) i; rwa [hTp, ← sub_zero (ka.aM (tt τ) i : ℤ)] at this) (hF.2.2 (tt τ))
    rw [hn] at bP
    exact And.intro (GlobalTheory.RunWeightDom.row hpq Tn (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) _ _ _ _ (laR T j wL k τ) (laR T j wF k τ) (Int.natCast_nonneg _)
      (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.1 bP.2.1 bP.2.2.1 bP.2.2.2
      bM.1 bM.2.1 bM.2.2.1 bM.2.2.2)
      (row_pair hpq (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (Int.natCast_nonneg _)
        (fun i => (ext0 (wL.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wL.aM (tt τ)) i : ℤ))
        (fun i => (ext0 (wF.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wF.aM (tt τ)) i : ℤ))
        (laR T j wL k τ) (laR T j wF k τ) (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.2.2.2 bM.2.2.2)
  rw [← hp0] at key hq
  have hq' : ((T.U j T.σ₀).X k).p0 < D.R.r := by omega
  have e : ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (c : Fin D.R.r),
      (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) τ c =
        laR T j wF k τ c - (2 * (c : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ c := by
    intro τ c
    exact expand_weight _ _ _ τ c
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, fun τ a b hab hb => ?_, fun τ a b ha hb => ?_⟩
  · obtain ⟨⟨k1, k2, -, -, -⟩, -⟩ := key τ
    have hab' : (a : ℕ) < b := by omega
    by_cases hc : (b : ℕ) < ((T.U j T.σ₀).X k).p0
    · have := k1 a b hab' hc; omega
    · have := k2 a b (by omega) hab'; omega
  · obtain ⟨⟨-, -, -, k4, -⟩, -⟩ := key τ
    have := k4 a b (by omega) (by omega)
    have h' : (19 : ℝ) * Tn ≤ 10 * ((laR T j wL k τ b - laR T j wL k τ a : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  · obtain ⟨⟨-, -, k3, -, -⟩, -⟩ := key τ
    have := k3 a b hab hb
    rw [e τ a, e τ b]
    linarith
  · obtain ⟨-, k5⟩ := key τ
    have := k5 a b ha hb hp hq
    rw [e τ a, e τ b]
    have h1 : (1 : ℤ) ≤ (laR T j wF k τ b - (2 * (b : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ b) -
      (laR T j wF k τ a - (2 * (a : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ a) := this
    exact_mod_cast h1

theorem archOne_of_run (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hpar : ParOK T EX p j) (hpg : PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0)
    (hC : HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus)
    (hjm : j < D.R.m) :
    ∀ k : (T.U j T.σ₀).Comp, ArchOne ((T.U j T.σ₀).X k) (GlobalTheory.Shares.laR T j wL k) (GlobalTheory.Shares.laR T j wF k) Tn := by
  obtain ⟨G, hG⟩ := GlobalTheory.RunJoin.exists_genOK D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar.orient hpg
  obtain ⟨i, et, he⟩ := GlobalTheory.EtaBoundForm.exists_etaOK D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpg hjm
  let G' := FamilyHypotheses.refill G G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  have hG' : GenOK h j hj large₂ G' _ _ := genOK_refill h j hj large₂ G _ _ hG G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  obtain ⟨A⟩ := GlobalTheory.RunJoin.archAt_of_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p _ nus hpar hpg hC hjm G' hG' he
  obtain ⟨t, -, ⟨Fl⟩⟩ := GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj _ wL wF G'.w Tn _ A
  intro k
  exact ⟨A.Xa k, A.hL k, A.hF k, A.hT k, A.mar k, ⟨Fl.Fl k⟩⟩

end Run

end GlobalTheory.ShareOn

end
