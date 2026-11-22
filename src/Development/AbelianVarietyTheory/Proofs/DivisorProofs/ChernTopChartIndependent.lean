import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

open Filter Topology AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ChernWeilLine

theorem cInfAt_eventually {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) : ∀ᶠ z in 𝓝 y, CInfAt f z := by
  obtain ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hW := (isOpen_ptsIn (p := p) (σ := σ) W).mem_nhds h₁
  have hc : ContinuousAt (fun z a => ev p σ W (g a) z) y :=
    continuousAt_pi.2 fun a => (continuousOn_ev (g a)).continuousAt hW
  filter_upwards [hW, hc.preimage_mem_nhds (h₂.mem_nhds h₃), h₅.eventuallyEq_nhds] with z hz hzO hz5
  exact ⟨W, ι, i, g, F, O, hz, h₂, hzO, h₄, hz5⟩

theorem chernTop_congr {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ)
    {G G' : V n → Mat m ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G') : chernTop R G v = chernTop R G' v := by
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => G u x.1) v x.2 = chernPoly (fun u => G' u x.1) v x.2 := by
    intro x
    unfold chernPoly curvPoly
    simp only [curv_congr (h.mono fun u hu => congrFun hu x.1)]
  simp only [chernTop, hc]

end GlobalTheory.ChernWeilLine

