import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.Points
open GlobalTheory.GradedPieces
open GlobalTheory.CechPic (cls)

namespace GlobalTheory.LocM

section Graded

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure IntChart (Z : Mdl Y i₀) : Type where

  U : Z.X.Opens

  aff : IsAffineOpen U

  w : Vecs Dw (Y Z.i).t Γ(Z.X, U)

  int : IntFrame Z aff w

theorem le_preimage_inf {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {U U' : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x ⁻¹ᵁ U') : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := fun _ hz => ⟨h hz, h' hz⟩

theorem valR_zero_fn {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) (U : X.Opens) : valR x U 0 = 0 := by
  unfold valR
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem spMap_valMap {X : Scheme.{0}} {R : Type} [CommRing R] {U : X.Opens} (hU : IsAffineOpen U) (x : Sp R ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : spMap (valMap x U h).hom ≫ hU.fromSpec = x := specMap_valMap_fromSpec hU x h

variable {Z : Mdl Y i₀}

theorem HasDR.exists_intChart (hZ : HasDR Z) (x : Z.X) : ∃ c : IntChart Z, x ∈ c.U :=
  have ⟨U, hU, w, hx, hw⟩ := hZ.2 x
  ⟨⟨U, hU, w, hw⟩, hx⟩

namespace IntChart

variable (c c' c'' : IntChart Z)

theorem aff_inf : IsAffineOpen (c.U ⊓ c'.U) := isAffineOpen_inf Z c.aff c'.aff

def vec {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    TanM (x ≫ Z.π) (Y Z.i).t.G :=
  tanOf (tan_bc c.int (valMap x _ h).hom (spMap_valMap c.aff x h) σ a)

theorem linearIndependent_vec {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) :
    LinearIndependent k (c.vec x h σ) := linInd_bc c.int _ (spMap_valMap c.aff x h) σ

theorem exists_tri (hZ : HasDR Z) (σ : E →+* ℂ) :
    ∃ m : Fin (Dw.mult σ) → Fin (Dw.mult σ) → Γ(Z.X, c.U ⊓ c'.U), (∀ a b, a < b → m a b = 0) ∧
      ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (a : Fin (Dw.mult σ)),
        c.vec x h σ a = ∑ b, valR x _ (m a b) • c'.vec x h' σ b := by
  obtain ⟨n, v, e, he, hv, hb⟩ := c'.int.1 σ
  have hV := c.aff_inf c'
  let ρ : Γ(Z.X, c.U) →+* Γ(Z.X, c.U ⊓ c'.U) := resG _ inf_le_left
  let ρ' : Γ(Z.X, c'.U) →+* Γ(Z.X, c.U ⊓ c'.U) := resG _ inf_le_right
  have hρ : spMap ρ ≫ c.aff.fromSpec = hV.fromSpec := c.aff.map_fromSpec hV _
  have hρ' : spMap ρ' ≫ c'.aff.fromSpec = hV.fromSpec := c'.aff.map_fromSpec hV _
  have hρ2 : spMap ρ' ≫ c'.aff.fromSpec ≫ Z.π = hV.fromSpec ≫ Z.π := by rw [← hρ', Category.assoc]
  choose q hq using fun a => (basis_map ρ' hρ2 hv hb _ (tan_bc c.int ρ hρ σ a)).exists
  have hx2 {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) :
      spMap (valMap x _ h').hom ≫ c'.aff.fromSpec ≫ Z.π = x ≫ Z.π := by
    rw [← Category.assoc, spMap_valMap]
  have key {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (a) :
      c.vec x h σ a = ∑ j, valR x _ (q a j) • tanOf (isTan_map _ (hx2 x h') (hv j)) := by
    have h3 : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U) := le_preimage_inf h h'
    have e1 : (valMap x _ h3).hom.comp ρ = (valMap x _ h).hom :=
      congrArg (fun f => f.hom) (res_valMap _ inf_le_left h3 h)
    have e2 : (valMap x _ h3).hom.comp ρ' = (valMap x _ h').hom :=
      congrArg (fun f => f.hom) (res_valMap _ inf_le_right h3 h')
    have hk := comb_map (valMap x _ h3).hom (x' := x ≫ Z.π)
      (by rw [← Category.assoc, spMap_valMap]) (hq a)
    simp only [Vecs.bc, dual_comp, e1, e2] at hk
    simp only [valR_eq x _ h3]
    exact (comb_iff (fun j => isTan_map _ (hx2 x h') (hv j)) _ (tan_bc c.int _ (spMap_valMap c.aff x h) σ a)).1 hk
  have ev {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (b) :
      tanOf (isTan_map _ (hx2 x h') (hv (e b))) = c'.vec x h' σ b :=
    tan_ext (by rw [vec, left_tanOf, left_tanOf, he b]; rfl)
  have zero (a j) (hj : ∀ b, e b = j → a < b) : q a j = 0 := fn_ext Z fun k _ x h3 ho => by
    have h := le_preimage_mono x inf_le_left h3
    have h' := le_preimage_mono x inf_le_right h3
    have p₁ := spMap_valMap c.aff x h
    have p₂ := spMap_valMap c'.aff x h'
    have f₁ := c.int.2 k (valMap x _ h).hom (by rw [p₁]; exact ho)
    have f₂ := c'.int.2 k (valMap x _ h').hom (by rw [p₂]; exact ho)
    rw [p₁] at f₁
    rw [p₂] at f₂
    obtain ⟨d, hd⟩ := exists_diag_of_flagAt Z hZ.1 f₁ f₂ σ
      (tan_bc c.int _ p₁ σ) (tan_bc c'.int _ p₂ σ) (linInd_bc c'.int _ p₂ σ)
    obtain ⟨cf, -, h0, hs⟩ := hd a
    have li := linInd_of_basis (fun j => isTan_map _ (hx2 x h') (hv j)) (basis_map _ (hx2 x h') hv hb)
    have e1 : ∑ b, cf b • tanOf (isTan_map _ (hx2 x h') (hv (e b))) =
        ∑ j, Function.extend e cf 0 j • tanOf (isTan_map _ (hx2 x h') (hv j)) :=
      Fintype.sum_of_injective e e.injective _ _
        (fun j hj => by rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply, zero_smul])
        (fun b => by rw [e.injective.extend_apply])
    simp only [ev] at e1
    rw [Fintype.linearIndependent_iffₛ.1 li _ _ ((key x h h' a).symm.trans (hs.trans e1)) j, valR_zero_fn]
    by_cases hj' : ∃ b, e b = j
    · obtain ⟨b, rfl⟩ := hj'
      rw [e.injective.extend_apply, h0 b (hj b rfl)]
    · rw [Function.extend_apply' _ _ _ hj', Pi.zero_apply]
  refine ⟨fun a b => q a (e b), fun a b hab => zero a _ fun b' hb' => by rwa [e.injective hb'], fun R _ x h h' a => ?_⟩
  rw [key x h h' a]
  refine (Fintype.sum_of_injective e e.injective _ _ (fun j hj => ?_) fun b => by rw [ev]).symm
  rw [zero a j fun b hb => (hj ⟨b, hb⟩).elim, valR_zero_fn, zero_smul]

variable (hZ : HasDR Z)

def chg (σ : E →+* ℂ) : Fin (Dw.mult σ) → Fin (Dw.mult σ) → Γ(Z.X, c.U ⊓ c'.U) := (c.exists_tri c' hZ σ).choose

theorem chg_eq_zero (σ : E →+* ℂ) {a b : Fin (Dw.mult σ)} (h : a < b) : c.chg c' hZ σ a b = 0 :=
  (c.exists_tri c' hZ σ).choose_spec.1 a b h

theorem vec_eq_sum {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : c.vec x h σ a = ∑ b, valR x _ (c.chg c' hZ σ a b) • c'.vec x h' σ b :=
  (c.exists_tri c' hZ σ).choose_spec.2 R x h h' a

theorem diag {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) (σ : E →+* ℂ) :
    Diag (c'.vec x h' σ) (c.vec x h σ) fun a => valR x _ (c.chg c' hZ σ a a) := fun a =>
  ⟨_, rfl, fun b hb => by rw [c.chg_eq_zero c' hZ σ hb, valR_zero_fn],
    c.vec_eq_sum c' hZ x h h' σ a⟩

theorem valR_chg_self {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    valR x _ (c.chg c hZ σ a a) = 1 :=
  congrFun ((c.diag c hZ x h h σ).unique (c.linearIndependent_vec x h σ) (Diag.refl _)) a

theorem valR_chg_mul {k : Type} [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (h'' : ⊤ ≤ x ⁻¹ᵁ c''.U) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    valR x _ (c.chg c' hZ σ a a) * valR x _ (c'.chg c'' hZ σ a a) = valR x _ (c.chg c'' hZ σ a a) :=
  congrFun (((c'.diag c'' hZ x h' h'' σ).trans (c.diag c' hZ x h h' σ)).unique (c''.linearIndependent_vec x h'' σ)
    (c.diag c'' hZ x h h'' σ)) a

theorem isUnit_chg (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : IsUnit (c.chg c' hZ σ a a) := by
  refine IsUnit.of_mul_eq_one (resG _ (inf_comm c.U c'.U).le (c'.chg c hZ σ a a)) (fn_ext Z fun k _ x h _ => ?_)
  have hi := le_preimage_mono x inf_le_left h
  rw [valR_mul x _ h, valR_res x _ h, valR_one x _ h, c.valR_chg_mul c' c hZ x hi (le_preimage_mono x inf_le_right h) hi,
    c.valR_chg_self hZ x hi]

def tr (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : Γ(Z.X, c.U ⊓ c'.U)ˣ :=
  ∏ σ, ∏ a, (c.isUnit_chg c' hZ σ a).unit ^ e σ a

theorem tr_add (e e' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : c.tr c' hZ (e + e') = c.tr c' hZ e * c.tr c' hZ e' := by
  simp only [tr, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

end IntChart

variable (hZ : HasDR Z) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ)

def grLB : LB Z.X := ⟨IntChart Z, IntChart.U, fun c c' => c.tr c' hZ e⟩

theorem valR_grLB {k : Type} [Field k] (x : Sp k ⟶ Z.X) (c c' : IntChart Z) {V : Z.X.Opens} (hV : V ≤ c.U ⊓ c'.U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : valR x V (res hV ((grLB hZ e).g c c')).val = ∏ σ, ∏ a, valR x _ (c.chg c' hZ σ a a) ^ e σ a :=
  (valR_res x hV h _).trans (valR_prod_zpow x (le_preimage_mono x hV h) _ e)

theorem isLB_grLB : (grLB hZ e).IsLB := by
  refine ⟨top_unique fun z _ => Opens.mem_iSup.2 (hZ.exists_intChart z), fun c => ?_, fun c c' c'' => ?_⟩
  · refine Units.ext (fn_ext Z fun k _ x h _ => (valR_grLB hZ e x c c _ h).trans ?_)
    simp only [c.valR_chg_self hZ x h, one_zpow, Finset.prod_const_one]
    exact (valR_one x _ h).symm
  · refine Units.ext (fn_ext Z fun k _ x h _ => (valR_mul x _ h _ _).trans ?_)
    refine (congrArg₂ (· * ·) (valR_grLB hZ e x c c' _ h) (valR_grLB hZ e x c' c'' _ h)).trans
      (.trans ?_ (valR_grLB hZ e x c c'' _ h).symm)
    simp only [← Finset.prod_mul_distrib, ← mul_zpow, c.valR_chg_mul c' c'' hZ x
      (le_preimage_mono x (inf_le_left.trans inf_le_left) h) (le_preimage_mono x (inf_le_left.trans inf_le_right) h)
      (le_preimage_mono x inf_le_right h)]

def grCls : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ CechPic.Pic Z.X :=
  AddMonoidHom.mk' (fun e => cls _ (isLB_grLB hZ e)) fun e e' => by
    have h := CechPic.isLB_tens (isLB_grLB hZ e) (isLB_grLB hZ e')
    refine (CechPic.cls_eq_iff _ h).2 (CechPic.iso_of_chart h ⟨fun c => (c, c), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' => ?_⟩)
    refine .trans ?_ (CechPic.gm_tens (grLB hZ e) (grLB hZ e') (𝟙 _) y (c, c) (c', c') ⟨hc, hc⟩ ⟨hc', hc'⟩).symm
    exact (congrArg _ (IntChart.tr_add c c' hZ e e')).trans (map_mul _ _ _)

end Graded

section Curves

structure Curve (k : Type) [Field k] (X : Scheme.{0}) : Type where

  n : ℕ

  I : (PSpace k n).IdealSheafData

  integral : IsIntegral I.subscheme

  dim : topologicalKrullDim I.subscheme = 1

  smooth : Smooth (I.subschemeι ≫ PSpace.str k n)

  f : I.subscheme ⟶ X

namespace Curve

variable {k : Type} [Field k] {X : Scheme.{0}} (c : Curve k X)

abbrev C : Scheme.{0} := c.I.subscheme

instance : IsIntegral c.C := c.integral

instance algebra : Algebra k Γ(c.C, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (c.I.subschemeι ≫ PSpace.str k c.n).appTop).hom.toAlgebra

theorem strHom_eq : strHom k c.C = c.I.subschemeι ≫ PSpace.str k c.n := GlobalTheory.strHom_eq fun _ => rfl

theorem isSmoothProjCurve : VB.IsSmoothProjCurve k c.C :=
  ⟨⟨c.integral, c.dim, c.n, _, inferInstance, c.strHom_eq.symm⟩, c.strHom_eq ▸ c.smooth⟩

theorem isProjCurve : VB.IsProjCurve k c.C := c.isSmoothProjCurve.toIsProjCurve

theorem exists_iso {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (h : VB.IsSmoothProjCurve k C) (f : C ⟶ X) :
    ∃ (c : Curve k X) (e : C ≅ c.C), e.hom ≫ c.f = f ∧ e.hom ≫ strHom k c.C = strHom k C := by
  obtain ⟨n, i, _, hi⟩ := h.isProjOver
  have hk : i.ker.subschemeι.ker = i.ker := Scheme.IdealSheafData.ker_subschemeι _
  have := IsClosedImmersion.isIso_lift _ _ hk
  let e := asIso (IsClosedImmersion.lift _ i hk.le)
  have he : e.hom ≫ i.ker.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  have hs : i.ker.subschemeι ≫ PSpace.str k n = e.inv ≫ strHom k C := by
    rw [Iso.eq_inv_comp, reassoc_of% he, hi]
  have := h.isIntegral
  have := h.smooth
  refine ⟨⟨n, i.ker, .of_isIso e.hom, ?_, hs ▸ inferInstance, e.inv ≫ f⟩, e, by simp, ?_⟩
  · exact (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans h.dim_eq
  · rw [strHom_eq]
    exact (congrArg (e.hom ≫ ·) hs).trans (by simp)

def degOf (L : LB X) : ℤ := VB.degLB k (L.pull c.f)

def degPic : CechPic.Pic X →+ ℤ := c.isProjCurve.degPic.comp (CechPic.pull c.f)

theorem degPic_cls {L : LB X} (hL : L.IsLB) : c.degPic (cls L hL) = c.degOf L := rfl

attribute [local instance] MvPolynomial.gradedAlgebra in
open ProjSpace ProjCoh in

theorem nonempty_of_point (x : Sp k ⟶ X) : Nonempty (Curve k X) :=
  (exists_iso (VB.isSmoothProjCurve_line k) (PSpace.str k 1 ≫ x)).nonempty

end Curve

end Curves

section OnModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {k : Type} [Field k] (c : Curve k Z.X)

namespace Curve

def t : SAB H c.C := (exists_sab (c.f ≫ Z.π) (Y Z.i).t).choose

variable (hZ : HasDR Z)

def degGr : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ ℤ := c.degPic.comp (grCls hZ)

end Curve

end OnModel

section Place

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

theorem hasDR : HasDR ct.YY := ct.isYY.2.1

def Fbar (ct : At S κ p) : Type := haveI := Fact.mk ct.hp; AlgebraicClosure (ZMod p)

instance : Field ct.Fbar := haveI := Fact.mk ct.hp; inferInstanceAs (Field (AlgebraicClosure (ZMod p)))

instance : IsAlgClosed ct.Fbar := haveI := Fact.mk ct.hp; inferInstanceAs (IsAlgClosed (AlgebraicClosure (ZMod p)))

instance : CharP ct.Fbar p := haveI := Fact.mk ct.hp; inferInstanceAs (CharP (AlgebraicClosure (ZMod p)) p)

abbrev Crv : Type := Curve ct.Fbar ct.YY.X

abbrev CrvQ : Type := Curve (AlgebraicClosure κ.c.F) ct.YY.X

open Classical in

def indWt (τ : PsiT D) (i : ℕ) : PsiT D → ℕ → ℤ := fun τ' i' => if τ' = τ ∧ i' = i then 1 else 0

def degPiece {k : Type} [Field k] (c : Curve k ct.YY.X) (τ : PsiT D) (i : ℕ) : ℤ :=
  c.degGr ct.hasDR (-ct.expo (indWt τ i))

def degLie {k : Type} [Field k] (c : Curve k ct.YY.X) (τ : PsiT D) : Bool → ℤ
  | false => ∑ i ∈ Finset.Icc 1 j, ct.degPiece c τ i
  | true => -∑ i ∈ Finset.Icc (j + 1) N, ct.degPiece c τ i

def degWt {k : Type} [Field k] (c : Curve k ct.YY.X) (l : PsiT D → ℕ → ℝ) : ℝ :=
  -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (ct.degPiece c τ i : ℝ)

def nefQ (l : PsiT D → ℕ → ℝ) : Prop := ∀ c : ct.CrvQ, 0 ≤ ct.degWt c l

end At

def embOf (D : D7) (τ : PsiT D) : D.host.E →+* ℂ := DV.tauEmb D (D.eTau.symm τ)

namespace At

end At

end Place

end GlobalTheory.LocM
