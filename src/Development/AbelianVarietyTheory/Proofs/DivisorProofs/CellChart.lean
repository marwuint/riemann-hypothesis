import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open Set

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CellChart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ}

include w in

theorem algX_eq {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) :
    (π.appLE U W hW).hom.comp (algX q U) = algX p W := by
  subst w
  have e := Scheme.Hom.appLE_comp_appLE π q ⊤ U W le_top hW
  exact congrArg (fun f ↦ (CommRingCat.Hom.hom f).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) e

variable {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) {N : Type} (n : N → Γ(Y, W))
  (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))

def cellHom {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) : Γ(Y, W) →+* ℂ :=
  (MvPolynomial.eval₂Hom (evHom hb) z).comp (RingEquiv.ofBijective _ hΦ).symm.toRingHom

theorem cellHom_appLE {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) (g : Γ(B, U)) :
    cellHom π hW n hΦ hb z ((π.appLE U W hW).hom g) = evHom hb g := by
  have e : (RingEquiv.ofBijective _ hΦ).symm ((π.appLE U W hW).hom g) = MvPolynomial.C g := by
    rw [RingEquiv.symm_apply_eq]; simp
  simp only [cellHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
    MvPolynomial.eval₂Hom_C]

end GlobalTheory.CellChart

namespace GlobalTheory.CellChart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) (hWa : IsAffineOpen W) {N : Type}
  (n : N → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))

def cellPt {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) : CxPts p σ :=
  ofHom hWa (cellHom π hW n hΦ hb z) fun a => by
    rw [← algX_eq π w hW, RingHom.comp_apply, cellHom_appLE, ← ev_eq hb, ev_algX hb]

theorem cellPt_mem {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) :
    cellPt π w hW hWa n hΦ hb z ∈ ptsIn p σ W := ofHom_mem _ _ _

end GlobalTheory.CellChart

namespace GlobalTheory.CellChart

section Chart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {ι : Type} {r : ι → ℕ} {d : ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))

variable (c : AlgChart q σ 1) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W)
  (n : (Σ a, Low (r a)) → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n))
  (y₀ : CxPts p σ)

def inv (v : V (d + 1)) : CxPts p σ :=
  if h : base e v ∈ c.e.target then
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun s => v (e.symm (some s)))
  else y₀

variable {e c hW hWa n hΦ}

theorem inv_eq {v : V (d + 1)} (h : base e v ∈ c.e.target) : inv π w e c hW hWa n hΦ y₀ v =
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun s => v (e.symm (some s))) := dif_pos h

theorem inv_mem {v : V (d + 1)} (h : base e v ∈ c.e.target) : inv π w e c hW hWa n hΦ y₀ v ∈ ptsIn p σ W := by
  rw [inv_eq _ _ _ h]; exact cellPt_mem ..

end Chart

end GlobalTheory.CellChart

namespace GlobalTheory.CellChart

end GlobalTheory.CellChart

