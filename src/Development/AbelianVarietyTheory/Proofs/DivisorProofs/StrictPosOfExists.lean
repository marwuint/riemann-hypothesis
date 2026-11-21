import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AlgChart

variable (c c' : AlgChart p σ D) {S : Set (CxPts p σ)} {y : CxPts p σ} {f g : CxPts p σ → ℝ}

def levi (f : CxPts p σ → ℝ) (y : CxPts p σ) (ξ : Fin D → ℂ) : ℝ :=
  (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

def dtrans (y : CxPts p σ) (ξ : Fin D → ℂ) : Fin D → ℂ :=
  fun b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (WithLp.toLp 2 ξ) b

variable {c c'}

theorem levi_congr (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S) (h : ∀ z ∈ S, f z = g z)
    (ξ : Fin D → ℂ) : c.levi f y ξ = c.levi g y ξ :=
  congrArg Complex.re (leviV_congr (eventually_of_mem
    ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      congrArg Complex.ofReal (h _ hv.2)) ξ)

theorem levi_add (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y))
    (hg : ContDiffAt ℝ 2 (g ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => f z + g z) y ξ = c.levi f y ξ + c.levi g y ξ :=
  (congrArg Complex.re (flA_leviV_add hf hg ξ)).trans (Complex.add_re _ _)

theorem levi_const_mul (a : ℝ) (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => a * f z) y ξ = a * c.levi f y ξ :=
  (congrArg Complex.re (LocalMaximumSecondDerivative.leviV_ofReal_const_mul a hf ξ)).trans (Complex.re_ofReal_mul _ _)

theorem levi_log_normSq {u : CxPts p σ → ℂ} (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S)
    (hu : DifferentiableOn ℂ (u ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) (h0 : u y ≠ 0)
    (ξ : Fin D → ℂ) : c.levi (fun z => Real.log (‖u z‖ ^ 2)) y ξ = 0 :=
  congrArg Complex.re (flA_leviV_log_normSq (h := u ∘ c.e.symm)
    (eventually_of_mem ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      hu.differentiableAt ((isOpen_over c.e hS).mem_nhds hv))
    (by rwa [Function.comp_apply, c.e.left_inv hy]) ξ)

theorem levi_trans (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source)
    (hf : ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e y)) (ξ : Fin D → ℂ) :
    c.levi f y ξ = c'.levi f y (c.dtrans c' y ξ) := by
  have ho := isOpen_over c.e c'.e.open_source
  have hn := ho.mem_nhds (mem_over c.e hy hy')
  have ht : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
    (((contDiffOn_piLp 2).2 fun a => contDiffOn_of_differentiableOn D _ _ ho
      (differentiableOn_euclidean.1 (c.holo_trans c') a)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have e : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hU : ContDiffAt ℝ 2 (fun v => (f (c'.e.symm v) : ℂ)) ((c'.e ∘ c.e.symm) (c.e y)) :=
    e ▸ Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have := flA_leviV_comp hU ht ξ
  rw [e] at this
  refine congrArg Complex.re (Eq.trans (leviV_congr (eventually_of_mem hn fun v hv => ?_) ξ) this)
  simp only [Function.comp_apply, c'.e.left_inv hv.2]

theorem dtrans_ne_zero (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) {ξ : Fin D → ℂ}
    (hξ : ξ ≠ 0) : c.dtrans c' y ξ ≠ 0 := fun h => by
  have hd : transDet c.e c'.e y ≠ 0 := rv_chart c c' hy hy' ▸
    rv_ne_zero _ _ (c.source_subset hy) (c'.source_subset hy')
  have hi := (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  have := LinearMap.ker_eq_bot'.1 hi (WithLp.toLp 2 ξ) (PiLp.ext fun b => congrFun h b)
  exact hξ (congrArg WithLp.ofLp this)

end AlgChart

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)} {y : CxPts p σ}

theorem SmoothOn.contDiffAt_two {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S)
    {c : AlgChart p σ D} (hy : y ∈ c.e.source) (hyS : y ∈ S) :
    ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) :=
  ((h.chart hS c).contDiffAt ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS))).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem levi_eq_of_add_log {f g : CxPts p σ → ℝ} {u : CxPts p σ → ℂ} (hS : IsOpen S)
    (hf : R.SmoothOn S f) (hu : R.HoloOn S u) (h0 : ∀ z ∈ S, u z ≠ 0)
    (h : ∀ z ∈ S, g z = f z + Real.log (‖u z‖ ^ 2)) {c : AlgChart p σ D} (hy : y ∈ c.e.source)
    (hyS : y ∈ S) (ξ : Fin D → ℂ) : c.levi g y ξ = c.levi f y ξ := by
  rw [AlgChart.levi_congr hS hy hyS h, AlgChart.levi_add (hf.contDiffAt_two hS hy hyS)
    ((hu.smoothOn_log hS h0).contDiffAt_two hS hy hyS),
    AlgChart.levi_log_normSq hS hy hyS (hu.chart hS c) (h0 y hyS), add_zero]

end AnRead

namespace Weight

open AnRead

variable {R R' : AnRead p σ D} {A B : LB Y} {φ : Weight p σ B} {ψ : Weight p σ A}
  {c : AlgChart p σ D} {y : CxPts p σ}

theorem IsSmooth.contDiffAt_two (h : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) : ContDiffAt ℝ 2 (φ.φ i ∘ c.e.symm) (c.e y) :=
  (h i).contDiffAt_two (isOpen_ptsIn _) hy hi

theorem IsSmooth.levi_frame (h : φ.IsSmooth R) {i j : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) (ξ : Fin D → ℂ) :
    c.levi (φ.φ i) y ξ = c.levi (φ.φ j) y ξ :=
  levi_eq_of_add_log ((isOpen_ptsIn (B.U i)).inter (isOpen_ptsIn (B.U j)))
    ((h j).mono inter_subset_right) (u := gv p σ B i j)
    (holoOn_ev_of_subset _ fun _ => mem_ptsIn_inf.2) (fun _ hz => gv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [φ.trans i j z hz.1 hz.2, sub_add_cancel]) hy ⟨hi, hj⟩ ξ

theorem SemiPos.chart (h : φ.SemiPos R) (hs : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) (ξ : Fin D → ℂ) : 0 ≤ c.levi (φ.φ i) y ξ := by
  obtain ⟨j, hj⟩ := R.cover y
  rw [AlgChart.levi_trans hy hj (hs.contDiffAt_two hj hi)]
  exact h i j y ⟨hj, hi⟩ _

theorem IsSmooth.strictPos_of_exists (hs : φ.IsSmooth R)
    (h : ∀ y, ∃ (c : AlgChart p σ D) (i : B.ι), y ∈ c.e.source ∧ y ∈ ptsIn p σ (B.U i) ∧
      ∀ ξ, ξ ≠ 0 → 0 < c.levi (φ.φ i) y ξ) : φ.StrictPos R := fun j c' y hy ξ hξ => by
  obtain ⟨c, i, hc, hi, h⟩ := h y
  exact (h _ (AlgChart.dtrans_ne_zero hy.1 hc hξ)).trans_eq ((hs.levi_frame hc hi hy.2 _).trans
    (AlgChart.levi_trans hy.1 hc (hs.contDiffAt_two hc hy.2) ξ).symm)

theorem levi_tens (hψ : ψ.IsSmooth R) (hφ : φ.IsSmooth R) {i : (CechPic.tens A B).ι}
    (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ ((CechPic.tens A B).U i)) (ξ : Fin D → ℂ) :
    c.levi ((ψ.tens φ).φ i) y ξ = c.levi (ψ.φ i.1) y ξ + c.levi (φ.φ i.2) y ξ :=
  AlgChart.levi_add (hψ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).1)
    (hφ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).2) ξ

theorem levi_zpow (hφ : φ.IsSmooth R) (n : ℤ) {j : PUnit → B.ι} (hy : y ∈ c.e.source)
    (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) (ξ : Fin D → ℂ) :
    c.levi ((φ.zpow n).φ j) y ξ = n * c.levi (φ.φ (j PUnit.unit)) y ξ := by
  rw [funext (φ.zpow_φ n j)]
  exact AlgChart.levi_const_mul _ (hφ.contDiffAt_two hy hj) ξ

theorem SemiPos.tens (h' : ψ.SemiPos R) (h : φ.SemiPos R) (hψ : ψ.IsSmooth R)
    (hφ : φ.IsSmooth R) : (ψ.tens φ).SemiPos R := fun i c y hy ξ =>
  (add_nonneg (h' _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).1⟩ ξ)
    (h _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).2⟩ ξ)).trans_eq (levi_tens hψ hφ hy.1 hy.2 ξ).symm

theorem SemiPos.zpow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) {n : ℤ} (hn : 0 ≤ n) :
    (φ.zpow n).SemiPos R := fun j c y hy ξ =>
  (mul_nonneg (Int.cast_nonneg hn) (h _ c y ⟨hy.1, mem_pow_iff.1 hy.2⟩ ξ)).trans_eq
    (levi_zpow hφ n hy.1 (mem_pow_iff.1 hy.2) ξ).symm

theorem SemiPos.pow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) (n : ℕ) : (φ.pow n).SemiPos R :=
  h.zpow hφ (Int.natCast_nonneg n)

end Weight

namespace WeightFamily.Reading

end WeightFamily.Reading

end GlobalTheory
