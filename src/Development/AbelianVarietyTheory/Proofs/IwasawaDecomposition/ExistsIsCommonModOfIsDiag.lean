import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransitionUniqueAndPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.MapComp

namespace GlobalTheory.LocM.CommonMod

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_lift (i : Idx H p) {k : Type} [Field k] (x : Sp k ⟶ (Y i).X) (f : i.c.F →+* k)
    (hf : x ≫ (Y i).s = spMap (f.comp (i.c.V W).subtype)) (hx : Set.range x ⊆ Set.range (Y i).j) :
    ∃ y : Sp k ⟶ (Xo i.l).XF i.c, y ≫ (Y i).j = x ∧ y ≫ pullback.snd _ _ = spMap f := by
  have : IsPreimmersion (spMap (i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (S := i.c.F) (nonZeroDivisors (i.c.V W))
  have := (Y i).jQ_open
  let z : Sp k ⟶ pullback (Y i).s (spMap (i.c.V W).subtype) :=
    pullback.lift x (spMap f) (hf.trans (sp_comp _ _).symm)
  have hz : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hr : Set.range z ⊆ Set.range (Y i).jQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hx ⟨a, rfl⟩
    refine ⟨b, (pullback.fst (Y i).s (spMap (i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hz]
    exact hb
  have e := IsOpenImmersion.lift_fac (Y i).jQ z hr
  refine ⟨IsOpenImmersion.lift (Y i).jQ z hr, ?_, ?_⟩
  · rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, e, hz]
  · rw [← (Y i).jQ_over, ← Category.assoc, e]
    exact pullback.lift_snd _ _ _

theorem exists_lift_chart (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} (h : spMap φ ≫ Z.chart a = w) :
    ∃ y : Sp k ⟶ (Xo Z.i.l).XF Z.i.c, y ≫ (Y Z.i).j = w ≫ Z.π ∧ y ≫ pullback.snd _ _ = spMap (φ.comp (Z.alg a)) := by
  refine exists_lift Z.i _ _ (by rw [Category.assoc, Z.π_s, ← h, Category.assoc, Z.affineOpenChart_comp_structure_eq_spMap]) ?_
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply]
  refine Z.cover.le (Set.mem_iUnion.2 ⟨a, ?_⟩)
  exact (Z.U a).2.range_fromSpec.le ⟨spMap φ x, by rw [← h]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem flagAt_push {Z₁ Z₂ : Mdl Y i₀} (hty : ∀ σ, Z₂.ty σ ⊆ Z₁.ty σ) {k : Type} [Field k] {w₁ : Sp k ⟶ Z₁.X}
    {w₂ : Sp k ⟶ Z₂.X} {τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X} (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ)
    (e : w₂ ≫ Z₂.π = w₁ ≫ Z₁.π ≫ τ) {u v : Vecs Dw (Y Z₁.i).t k} (hu : Z₁.FlagAt w₁ u) (hv : Z₁.FlagAt w₁ v)
    (h : Z₂.FlagAt w₂ fun σ j => u σ j ≫ mu.φ) : Z₂.FlagAt w₂ fun σ j => v σ j ≫ mu.φ := by
  obtain ⟨b, ψ, hb, fu, su⟩ := h
  obtain ⟨c, k₁, k₂, k₃⟩ := flagAt_two Z₁ hu hv
  rw [← Category.assoc] at e
  have fr : IsFrame (Y Z₂.i).t (ψ.comp (Z₂.alg b)) (w₂ ≫ Z₂.π) (Dw := Dw) fun σ j => v σ j ≫ mu.φ := by
    rw [e] at fu ⊢
    exact isFrame_push mu k₁ k₂ fu
  have sf := sameFlag_push mu hty k₃
  rw [← e] at sf
  exact ⟨b, ψ, hb, fr, sameFlag_trans (tan_chart Z₂ hb) (fun σ j => (fu.1 σ j).1) (fun σ j => (fr.1 σ j).1) su sf⟩

theorem natImg_unique {Z₁ Z₂ : Mdl Y i₀} (h : LocM.Corr Z₁ Z₂) {k : Type} [Field k] {w₁ : Sp k ⟶ Z₁.X}
    {w₂ w₂' : Sp k ⟶ Z₂.X} (hf : NatImg Z₁ Z₂ w₁ w₂) (hg : NatImg Z₁ Z₂ w₁ w₂') : w₂ = w₂' := by
  obtain ⟨τ, mu, u, t, e, fu, fu'⟩ := hf
  obtain ⟨τ', mu', v, t', e', fv, fv'⟩ := hg
  obtain ⟨rfl, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ' mu mu' h.2.1 t t'
  have fv₀ := fv
  obtain ⟨a, φ, ha, gv, -⟩ := fv₀
  obtain ⟨y, hy, -⟩ := exists_lift_chart Z₁ ha
  have ev : (fun σ j => v σ j ≫ mu'.φ : Vecs Dw (Y Z₂.i).t k) = fun σ j => v σ j ≫ mu.φ :=
    funext fun σ => funext fun j => (hmu k y _ _ _ (by rw [hy]; exact (gv.1 σ j).1.1)).symm
  rw [ev] at fv'
  have f₂ := flagAt_push h.2.2 mu e fu fv fu'
  have f₃ := f₂
  obtain ⟨b, ψ, hb, g, -⟩ := f₃
  obtain ⟨y₂, hy₂, hs⟩ := exists_lift_chart Z₂ hb
  rw [← hy₂] at g
  exact (Z₂.bij k _ y₂ hs _ g).unique ⟨hy₂.symm, f₂⟩ ⟨(e'.trans e.symm).trans hy₂.symm, fv'⟩

theorem comp_π_eq {M Z : Mdl Y i₀} {f : M.X ⟶ Z.X} (hf : IsMap M Z f) {τ : (Y M.i).X ⟶ (Y Z.i).X}
    {mu : SABMap (Y M.i).t (Y Z.i).t τ} (t : IsTrans Z.i M.i τ mu) : f ≫ Z.π = M.π ≫ τ := by
  have := M.normal
  have : IsReduced M.X := GlobalTheory.IsNormalScheme.isReduced
  have := Toroidal.isProper_toroidalModel_structureMap (Y Z.i)
  have : IsSeparated ((Y Z.i).s ≫ terminal.from _) := inferInstance
  refine ext_of_fromSpecResidueField_eq _ _ ((Y Z.i).s ≫ terminal.from _) M.opn M.dense (fun x hx => ?_)
    (terminal.hom_ext _ _)
  obtain ⟨τ', mu', -, t', e, -⟩ := hf.2 (M.X.residueField x) (M.X.fromSpecResidueField x) (by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply x a).symm ▸ hx)
  obtain ⟨rfl, -⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ' mu mu' hf.1.2.1 t t'
  exact (Category.assoc _ _ _).symm.trans e

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

end GlobalTheory.LocM.CommonMod
