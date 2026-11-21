import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField Filter Topology TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Points
open scoped ContDiff

namespace GlobalTheory.MetFam

section Fam

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def FamAt (t : ℝ → ℝ) (u : ℝ → CxPts p σ → F) (u₀ : CxPts p σ → F) (y : CxPts p σ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : CxPts p σ → ι → ℂ) (Φ : ℝ × (ι → ℂ) → F) (O : Set (ℝ × (ι → ℂ))),
    VInfAt f y ∧ IsOpen O ∧ (0, f y) ∈ O ∧ ContDiffOn ℝ ∞ Φ O ∧ (u₀ =ᶠ[𝓝 y] fun z => Φ (0, f z)) ∧
      ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, u x.1 x.2 = Φ (t x.1, f x.2)

variable {t : ℝ → ℝ} {u u' : ℝ → CxPts p σ → F} {u₀ u₀' : CxPts p σ → F} {y : CxPts p σ}

theorem FamAt.comp (h : FamAt t u u₀ y) {Ψ : F → G} {T : Set F} (hT : IsOpen T) (hy : u₀ y ∈ T)
    (hΨ : ContDiffOn ℝ ∞ Ψ T) : FamAt t (fun R z => Ψ (u R z)) (fun z => Ψ (u₀ z)) y := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨ι, inferInstance, f, Ψ ∘ Φ, O ∩ Φ ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, mem_preimage.2 (h₅.self_of_nhds ▸ hy :)⟩, hΨ.comp (h₄.mono inter_subset_left) fun _ hv => hv.2,
    h₅.fun_comp Ψ, h₆.mono fun _ hx => congrArg Ψ hx⟩

theorem FamAt.comp_contDiff (h : FamAt t u u₀ y) {Ψ : F → G} (hΨ : ContDiff ℝ ∞ Ψ) :
    FamAt t (fun R z => Ψ (u R z)) (fun z => Ψ (u₀ z)) y := h.comp isOpen_univ trivial hΨ.contDiffOn

theorem FamAt.prodMk {v : ℝ → CxPts p σ → G} {v₀ : CxPts p σ → G} (h : FamAt t u u₀ y) (h' : FamAt t v v₀ y) :
    FamAt t (fun R z => (u R z, v R z)) (fun z => (u₀ z, v₀ z)) y := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  obtain ⟨ι', _, f', Φ', O', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := h'
  have cl : ContDiff ℝ ∞ fun (x : ℝ × (ι ⊕ ι' → ℂ)) => (x.1, fun a => x.2 (.inl a)) :=
    contDiff_fst.prodMk (contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ _).comp contDiff_snd)
  have cr : ContDiff ℝ ∞ fun (x : ℝ × (ι ⊕ ι' → ℂ)) => (x.1, fun a => x.2 (.inr a)) :=
    contDiff_fst.prodMk (contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ _).comp contDiff_snd)
  refine ⟨ι ⊕ ι', inferInstance, fun z => Sum.elim (f z) (f' z),
    fun x => (Φ (x.1, fun a => x.2 (.inl a)), Φ' (x.1, fun a => x.2 (.inr a))),
    (fun x => (x.1, fun a => x.2 (.inl a))) ⁻¹' O ∩ (fun x => (x.1, fun a => x.2 (.inr a))) ⁻¹' O',
    vInfAt_pi fun a => ?_, (h₂.preimage cl.continuous).inter (h₂'.preimage cr.continuous), ⟨h₃, h₃'⟩,
    (h₄.comp cl.contDiffOn fun _ hv => hv.1).prodMk (h₄'.comp cr.contDiffOn fun _ hv => hv.2), ?_, ?_⟩
  · rcases a with a | a
    exacts [h₁.comp_contDiff (contDiff_apply ℝ ℂ a), h₁'.comp_contDiff (contDiff_apply ℝ ℂ a)]
  · filter_upwards [h₅, h₅'] with z e e' using Prod.ext e e'
  · filter_upwards [h₆, h₆'] with z e e' using Prod.ext e e'

end Fam

open GlobalTheory.ShFam GlobalTheory.Toroidal
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.QCoh (pullbackSections)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

end GlobalTheory.MetFam

end
