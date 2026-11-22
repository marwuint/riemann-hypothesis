import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAdd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.RankBd

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem pnorm_fac_pos (Y : Data D.host.E r) (la : Wt Y.Ψ r) {x : Frame Y.Ψ r} (hx : x ∈ Y.dom) :
    0 < ∏ τ, ∏ i : Fin r, ‖dmin Y.Gm x τ i.succ / dmin Y.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  have hne : ∀ τ i, dmin Y.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))

theorem eLpNorm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hm : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x, f x ≤ B) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
  have hint : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hm.pow 2) (B ^ 2) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (hf0 x) (hB x) 2)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity),
    eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x), ← ENNReal.ofReal_pow (hf0 x)]

open scoped TensorProduct

open scoped TensorProduct

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem finrank_le_of_sup (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r) (la : ∀ k, Wt (X k).Ψ r)
    {Kf : Subgroup (GA D V)} {th : ∀ k, (X k).Ψ → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} {N : ℕ} (hN : 0 < N) (hth : ∀ k τ, StandardLattice.IsInfEmb τ.1 (th k τ))
    (hd : DictIsUnif V dict Kf th hr) (hK : IsLevelK V N Kf)
    (hu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (S : Submodule ℂ (FDSec X))
    (hS : ∀ P ∈ S, P ∈ holSub X la ∧ (∀ k, ContinuousOn (P k) (X k).dom) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) ∧ (∀ k x, x ∉ (X k).dom → P k x = 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ P ∈ S, supE X la P ^ 2 ≤ ENNReal.ofReal C * petE V dict (muQ1 V) la P ^ 2) :
    FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ C := by

  have hpt : ∀ (P : FDSec X) (g : GA D V), ptN la P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom := hd.2.2.2.1
  have hle : ∀ (P : FDSec X) (g : GA D V), ENNReal.ofReal ‖P (dict g).1 (dict g).2‖ ≤ supE X la P := fun P g => by
    rw [← hpt]
    exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) ⟨(dict g).1, ⟨_, hdom g⟩⟩
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) (muQ1 V) := by
    intro P hP
    obtain ⟨-, hc, hΓ, -⟩ := hS P hP
    have hmu : MuUnit V dict (fun _ => 1) := ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩
    have h := GlobalTheory.PeterssonCompare.measurable_onQ_adel V hN hth hd hK hmu continuous_const P hc hΓ
    have e : (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) = fun q => ‖onQ V (adel V dict (fun _ => 1) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm.aestronglyMeasurable
  have hpet : ∀ P ∈ S, petE V dict (muQ1 V) la P ^ 2 =
      ENNReal.ofReal (∫ q, ‖P (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
    intro P hP
    have hfin := supE_ne_top X la (hS P hP).1
    have e : petE V dict (muQ1 V) la P = eLpNorm (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) 2 (muQ1 V) := by
      unfold petE
      congr 1
      funext q
      exact hpt P _
    rw [e]
    exact eLpNorm_sq_eq (fun _ => norm_nonneg _) (hmeas P hP) (B := (supE X la P).toReal) fun q =>
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hle P _)
  refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := muQ1 V)
    (fun q (P : S) => ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖)
    (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame (X (dict q.out).1).Ψ r => ℂ) (dict q.out).2 ∘ₗ
      LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) (dict q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
    (fun P => hmeas P P.2) ?_ hC ?_
  · intro P hP0
    have h0 : petE V dict (muQ1 V) la (P : FDSec X) = 0 := by
      have e : (fun q : AutQ V => ptN la (P : FDSec X) (dict q.out)) = fun _ => 0 := by
        funext q
        rw [hpt]
        exact hP0 q
      unfold petE
      rw [e]
      exact eLpNorm_zero
    have hs := hsup P P.2
    rw [h0] at hs
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, nonpos_iff_eq_zero,
      pow_eq_zero_iff] at hs
    obtain ⟨-, -, -, hoff⟩ := hS P P.2
    refine Subtype.ext (funext fun k => funext fun x => ?_)
    by_cases hx : x ∈ (X k).dom
    · have h1 : ENNReal.ofReal ((X k).pnorm (la k) ((P : FDSec X) k) x) ≤ supE X la P :=
        le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P : FDSec X) p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
      rw [hs, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      have h2 : ‖(P : FDSec X) k x‖ * _ ≤ 0 := h1
      have h3 := pnorm_fac_pos (X k) (la k) hx
      have h4 : ‖(P : FDSec X) k x‖ ≤ 0 := nonpos_of_mul_nonpos_left h2 h3
      simpa using h4
    · simpa using hoff k x hx
  · intro P q
    have h1 := hle (P : FDSec X) q.out
    have h2 := hsup P P.2
    rw [hpet P P.2] at h2
    have h3 : ENNReal.ofReal (‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2) ≤
        ENNReal.ofReal (C * ∫ q, ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hC]
      exact (pow_le_pow_left' h1 2).trans h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg fun _ => by positivity))).1 h3

open Module

end GlobalTheory.LevGeo.RankBd
