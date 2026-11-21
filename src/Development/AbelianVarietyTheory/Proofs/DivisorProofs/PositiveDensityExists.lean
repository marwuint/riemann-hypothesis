import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem transDet_trans_chart (c c' c'' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) (hy'' : y ∈ c''.e.source) :
    ChartGlue.transDet c.e c''.e y =
      ChartGlue.transDet c.e c'.e y * ChartGlue.transDet c'.e c''.e y := by
  have ho := ChartGlue.isOpen_over c.e (c'.e.open_source.inter c''.e.open_source)
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' (c'.e.source ∩ c''.e.source) :=
    ChartGlue.mem_over c.e hy ⟨hy', hy''⟩
  have e : c''.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (c''.e ∘ c'.e.symm) ∘ (c'.e ∘ c.e.symm) :=
    eventually_of_mem (ho.mem_nhds hm) fun w hw => by
      simp only [Function.comp_apply, c'.e.left_inv hw.2.1]
  have hf : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    (c.holo_trans c').differentiableAt
      ((ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hy hy'))
  have hfy : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := by simp [c.e.left_inv hy]
  have hg : DifferentiableAt ℂ (c''.e ∘ c'.e.symm) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [hfy]
    exact (c'.holo_trans c'').differentiableAt
      ((ChartGlue.isOpen_over c'.e c''.e.open_source).mem_nhds (ChartGlue.mem_over c'.e hy' hy''))
  rw [ChartGlue.transDet, e.fderiv_eq, fderiv_comp _ hg hf, hfy, ChartGlue.transDet,
    ChartGlue.transDet]
  simp only [ContinuousLinearMap.det]
  exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

theorem transDet_chart_ne_zero (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ChartGlue.transDet c.e c'.e y ≠ 0 := by
  intro h
  have := transDet_trans_chart c c' c hy hy' hy
  rw [c.transDet_self hy, h, zero_mul] at this
  exact one_ne_zero this

theorem continuousAt_transDet_chart (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ContinuousAt (ChartGlue.transDet c.e c'.e) y := by
  have hW : y ∈ ptsIn p σ (c.U ⊓ c'.U) :=
    mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩
  have h1 : ContinuousAt (ev p σ _ (c.isFrame.ratio c'.isFrame).val) y :=
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hW)
  refine h1.congr ?_
  filter_upwards [(c.e.open_source.inter c'.e.open_source).mem_nhds ⟨hy, hy'⟩] with z hz
  exact c.ev_ratio c' hz.1 hz.2

end GlobalTheory.CurveDens
