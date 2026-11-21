import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)
open H0

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' T : Scheme.{0}} {φ : Y' ⟶ Y}

section Ideal

variable {L : LB Y} {L' : LB Y'} {ι : Type}

theorem secGer_chartSec (l : ChartPull L' L φ) (s : ι → L.Sec) (j : L'.ι) (z : Y') (hj : z ∈ L'.U j)
    (i : ι) : secGer (fun i => chartSec l (s i)) j z hj i =
      (φ.stalkMap z).hom (secGer s (l.idx j) (φ z) (l.le j hj) i) :=
  ger_appLE φ (l.le j) z hj _

theorem stalkId_cutIdeal_chartSec (hL : L.IsLB) (hL' : L'.IsLB) (l : ChartPull L' L φ)
    (s : ι → L.Sec) (z : Y') : stalkId (cutIdeal hL' fun i => chartSec l (s i)) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom := by
  obtain ⟨j, hj⟩ := exists_chart hL' z
  rw [stalkId_cutIdeal hL' _ j z hj, stalkId_cutIdeal hL s _ _ (l.le j hj), Ideal.map_span,
    ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext (secGer_chartSec l s j z hj))

theorem stalkId_cutIdeal_secPull (hL : L.IsLB) (s : ι → L.Sec) (z : Y') :
    stalkId (cutIdeal (LB.isLB_pull hL φ) fun i => secPull (s i) φ) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom :=
  stalkId_cutIdeal_chartSec hL _ (GlobalTheory.chartPullPull L φ) s z

variable {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}

theorem le_ker_iff_stalk (t : T ⟶ Y) :
    I ≤ t.ker ↔ ∀ z, stalkId I (t z) ≤ RingHom.ker (t.stalkMap z).hom := by
  refine ⟨fun h z => ?_, fun h => Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_⟩
  · obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := t z) trivial
    rw [ds_stalkId_eq_map I W _ hW, Ideal.map_le_iff_le_comap]
    intro a ha
    have h₀ : (t.app W.1).hom a = 0 := t.ideal_ker_le W (h W ha)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hW a).trans ((congrArg _ h₀).trans (map_zero _))
  · refine fun_ext_ger (U := t ⁻¹ᵁ U.1) fun z hz => ?_
    have := h z ((mem_ideal_iff_ger I U a).1 ha _ hz)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hz a).symm.trans (this.trans (map_zero _).symm)

variable (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)
include hI

theorem le_ker_iff_comp (t : T ⟶ Y') : I' ≤ t.ker ↔ I ≤ (t ≫ φ).ker := by
  rw [le_ker_iff_stalk, le_ker_iff_stalk]
  refine forall_congr' fun z => ?_
  rw [hI, Ideal.map_le_iff_le_comap, RingHom.comap_ker, Scheme.Hom.stalkMap_comp]
  rfl

theorem le_map_of_stalk : I ≤ I'.map φ := (le_ker_iff_comp hI _).1 I'.ker_subschemeι.ge

theorem eq_comap_of_stalk : I' = I.comap φ :=
  le_antisymm ((le_ker_iff_comp hI _).2 (by
      rw [Limits.pullback.condition]
      exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)))
    (Scheme.IdealSheafData.le_map_iff_comap_le.1 (le_map_of_stalk hI))

end Ideal

section Symbol

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} (H : IsPullback φ p' p (spMap σ))

variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {L A B : LB Y} {L' A' B' : LB Y'} (l : ChartPull L' L φ) (a : ChartPull A' A φ)
  (b : ChartPull B' B φ) (s : Fin D → L.Sec)

abbrev pullQuotSec (e : (LB.div A (tw B L D)).Sec) : (LB.div A' (tw B' L' D)).Sec :=
  chartSec (chartPullQuot a (chartPullTwist b l D)) e

variable (hL : L.IsLB) (hA : A.IsLB) (hB : B.IsLB) (hL' : L'.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (e : (LB.div A (tw B L D)).Sec)

variable (hS : Etale ((cutIdeal hL s).subschemeι ≫ p))
  (hS' : Etale ((cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ p'))
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s))
  (he' : SuppIn (nonzeroLocus (pullQuotSec l a b e)) (cutIdeal hL' fun t => chartSec l (s t)))
  {ψ : (cutIdeal hL' fun t => chartSec l (s t)).subscheme ⟶ (cutIdeal hL s).subscheme}
  (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ φ)

variable {O : Y.Opens} {W : Y'.Opens} (hW : W ≤ φ ⁻¹ᵁ O) (hO : SuppIn O (cutIdeal hL s))
  (hO' : SuppIn W (cutIdeal hL' fun t => chartSec l (s t)))

end Symbol

end GlobalTheory.Vanishing
