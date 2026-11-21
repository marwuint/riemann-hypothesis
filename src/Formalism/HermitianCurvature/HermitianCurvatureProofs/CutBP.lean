import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbFormPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismLevels
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

theorem cptCoef_cutF {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (ε : ℝ) :
    KB.CptCoef Bs (D.cutF Bs χ F ε) := by
  refine ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hF.1 ε, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := hF.2.1
    exact ⟨R, fun g hg hne => hR g hg (fun h0 => hne (by simp [D.cutF, h0]))⟩
  · obtain ⟨e, he, hge⟩ := hF.2.2
    exact ⟨e, he, fun g hg hne => hge g hg (fun h0 => hne (by simp [D.cutF, h0]))⟩

theorem isBoundedBilinearMap_compR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wq) => q.1.comp q.2) where
  add_left x₁ x₂ y := ContinuousLinearMap.add_comp x₁ x₂ y
  smul_left c x y := by ext v; simp
  add_right x y₁ y₂ := ContinuousLinearMap.comp_add x y₁ y₂
  smul_right c x y := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply]
    exact ContinuousLinearMap.map_smul_of_tower x c (y v)
  bound := ⟨1, one_pos, fun x y => by simpa using ContinuousLinearMap.opNorm_comp_le x y⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_comp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    {A : B.Mat k r → (Wq →L[ℂ] Wq)} (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, A1, hU2, h2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (A1 g), hU1.inter hU2, ⟨h1, h2⟩, ?_, ?_⟩
  · exact isBoundedBilinearMap_compR.contDiff.comp_contDiffOn
      ((hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right))
  · intro x hx hxG
    simp only [he1 x hx.1 hxG, he2 x hx.2 hxG]

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem posAt_of_cpt (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y) (hF : KB.CptCoef p.T.base F) : TBB.PosAt p nn F Y N := by
  refine Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn ?_
  intro j w h hj hw _
  by_cases hh : D.IsLocPt h j
  · rw [PBL.rr_eq_form p F j hj w h h hh hh]
    obtain ⟨ε, hε, hnv⟩ := PBL.slv_nv p hF j hj w h hh
    exact Formalism.FourierDecayAlt.P.TBBx5.form_re_nonneg p
      (Formalism.FourierDecayAlt.P.TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p) j hj w hw.1 hε _ hnv
  · unfold KB.Pl.RR D.RRplace
    rw [dif_neg (fun h1 => hh h1.1)]
    simp

def LimE (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
      (𝓝 (sz * (B.beta p.T.base F F).re))

def LemB (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (κ₀ : ℝ) : Prop :=
  ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F

def Amaps (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
    (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ : ℕ) : Prop :=
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (TBB.Tq p / TBB.Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀)

def BigCellDerivativeExpansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) : Prop :=
  ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
    ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
    (∀ i, TBB.jN2 p (fi i) ≤ TBB.jN2 p f) ∧
    (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fi i) (P.r + 1) [] (TBB.bigPt P.r c))) ∧
    ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ((D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (TBB.bigPt P.r c) =
        ∑ i, co i • p.V (fi i) (TBB.bigPt P.r c)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
