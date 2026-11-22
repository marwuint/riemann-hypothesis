import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

open H0

variable {Y T : Scheme.{0}} {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'}
  {r : T ⟶ Y} {P B N : LB Y} {P' B' N' : LB T} {O : Y.Opens} {W : T.Opens}

theorem pullChart_ofSec (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (s : B.Sec) :
    pullChart a hq h (H0.ofSec p O s) = H0.ofSec q W (GlobalTheory.chartSec a s) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_pullChart, germ_ofSec]
    exact (congrArg _ (germ_ofSec _ _ _ _ s)).trans (ger_appLE r _ z hz.2 _).symm

theorem pullChart_mul (C : ProdChart P B N) (C' : ProdChart P' B' N') (a : ChartPull P' P r) (b : ChartPull B' B r)
    (c : ChartPull N' N r) (hC : ∀ t, ∃ s, a.idx (C'.a t) = C.a s ∧ b.idx (C'.b t) = C.b s ∧ c.idx (C'.c t) = C.c s)
    (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullChart c hq h (C.mul σ f) = C'.mul (pullChart a hq h σ) (pullChart b hq h f) :=
  C'.sec_ext fun t z hz ha hb hc => by
    obtain ⟨s, e₁, e₂, e₃⟩ := hC t
    have key (y hy i j l) (e₁ : i = C.a s) (e₂ : j = C.b s) (e₃ : l = C.c s) (hi hj hl) :
        germ l y hy hl (C.mul σ f) = germ i y hy hi σ * germ j y hy hj f := by
      subst e₁ e₂ e₃
      exact C.germ_mul σ f s y hy hi hj hl
    rw [C'.germ_mul _ _ t z hz ha hb hc, germ_pullChart, germ_pullChart, germ_pullChart, ← map_mul]
    exact congrArg _ (key _ _ _ _ _ e₁ e₂ e₃ _ _ _)

end GlobalTheory.Vanishing

namespace GlobalTheory.HermTools

end GlobalTheory.HermTools

namespace GlobalTheory.Adelic.HermSys

variable {F : Type} [Field F] [NumberField F] {T : HermSys F} (E : Type) [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.Adelic.HermSys

namespace GlobalTheory.HilbertSamuel

variable {F : Type} [Field F] [NumberField F]

namespace Geo

variable (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem toExt_mulW (j : ℕ) (u : Fin G.N → F) (f : G.Sec j) :
    G.toExt E (j + 1) (G.mulW j u f) = (G.baseChange E).mulW j (algebraMap F E ∘ u) (G.toExt E j f) := by
  refine (pullChart_mul _ (oneChart (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLBA) (G.baseChange E).isLB
    (Nat.cast_succ j).symm) (GlobalTheory.chartPullPull G.L (G.fst E)) (G.chartAdj E j) (G.chartAdj E (j + 1))
    (fun t => ⟨((t.1.1 PUnit.unit, t.1.2 PUnit.unit), t.2 PUnit.unit), rfl, rfl, rfl⟩) _ le_rfl _ f).trans ?_
  refine congrArg (fun s => ProdChart.mul _ s _) ?_
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (map_smulₛₗ _ _ _).trans (congrArg _ (pullChart_ofSec _ _ _ (G.b k)))

end Geo

namespace Data

variable {X : Data F} (E : Type) [Field E] [NumberField E] [Algebra F E]

variable (X) in

theorem toExtV_mem {j : ℕ} {x : X.V j} (hx : x ∈ X.M j) : X.toExtV E j x ∈ (X.baseChange E).M j :=
  (Submodule.subset_span ⟨x, hx, rfl⟩ : extMap (X.toExt E j) (X.V j) x ∈
    Submodule.span (𝓞 E) (extMap (X.toExt E j) (X.V j) '' X.M j))

theorem MulStable.baseChange (h : X.MulStable) : (X.baseChange E).MulStable := fun j hj w hw f hf => by
  let X' := X.baseChange E
  let S := (X'.M (j + 1)).map ((X'.V (j + 1)).subtype.restrictScalars (𝓞 E))
  change X'.mulW j w f ∈ S
  induction hw using Submodule.span_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul]; exact S.smul_mem _ ha
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    induction hf using Submodule.span_induction with
    | zero => exact (map_zero (X'.mulW j _)).symm ▸ zero_mem _
    | add a b _ _ ha hb => exact (map_add (X'.mulW j _) _ _).symm ▸ add_mem ha hb
    | smul c a _ ha =>
      exact (map_smul (X'.mulW j _) (algebraMap _ E c) _).symm ▸ S.smul_mem c ha
    | mem f hf =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, e⟩ := h j hj _ (Submodule.subset_span ⟨k, rfl⟩) f hf
      exact ⟨_, X.toExtV_mem E hg, (congrArg (X.toExt E (j + 1)) e).trans (X.toExt_mulW E j _ _)⟩

end Data

end GlobalTheory.HilbertSamuel
