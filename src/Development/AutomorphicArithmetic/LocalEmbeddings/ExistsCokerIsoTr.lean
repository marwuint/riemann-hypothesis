import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AutomorphicArithmetic.DivisorFrames.CokernelFrameCompatMono

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.FlagLocal GlobalTheory.LineQuot

namespace UpperTheory.Grass

section Basic

variable {X Y : Scheme.{0}} {A A' F : X.Modules}

def img (u : A ⟶ F) : Sub F := Sub.ker (cokernel.π u)

theorem same_img (u : A ⟶ F) [Mono u] : Same (img u).incl u := same_of_range fun V => by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact (cokernel_app_eq_zero_iff u V _).1 ((img u).incl_app_mem s)
  · rintro ⟨s, rfl⟩
    exact (img u).mem_sec_iff.1 ((cokernel_app_eq_zero_iff u V _).2 ⟨s, rfl⟩)

theorem sub_ext {N N' : Sub F} (h : Same N.incl N'.incl) : N = N' := by
  have key {N N' : Sub F} (h : Same N.incl N'.incl) (V : X.Opens) : N.sec V ≤ N'.sec V := by
    obtain ⟨e, he⟩ := h
    intro s hs
    exact (N'.exists_comp_incl_iff N.incl).1 ⟨e.hom, he⟩ V (N.mkSec s hs)
  obtain ⟨s, _, _⟩ := N
  obtain ⟨s', _, _⟩ := N'
  obtain rfl : s = s' := funext fun V => le_antisymm (key h V) (key h.symm V)
  rfl

theorem exists_cokerIso {u : A ⟶ F} {v : A' ⟶ F} (h : Same u v) :
    ∃ ψ : cokernel u ≅ cokernel v, cokernel.π u ≫ ψ.hom = cokernel.π v := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨cokernelEpiComp e.hom v, by simp⟩

theorem isVB_of_same {u : A ⟶ F} {v : A' ⟶ F} (h : Same u v) {m r : ℕ} (h₁ : IsVB A' m) (h₂ : IsVB (cokernel v) r) :
    IsVB A m ∧ IsVB (cokernel u) r :=
  have ⟨e, _⟩ := h
  have ⟨ψ, _⟩ := exists_cokerIso h
  ⟨h₁.of_iso e.symm, h₂.of_iso ψ.symm⟩

end Basic

variable {B : Scheme.{0}} {E : B.Modules} {m r : ℕ} {Z Z' Z'' : Scheme.{0}}

theorem cmp_id (g : Z ⟶ B) (w : 𝟙 Z ≫ g = g) :
    (cmp (𝟙 Z) g w).hom.app E = (Scheme.Modules.pullbackId Z).hom.app ((Scheme.Modules.pullback g).obj E) := by
  rw [cmp_hom_app]
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality g) E
  simp [Scheme.Modules.pullbackCongr] at this ⊢
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom] at this
  rw [this]
  exact (Category.comp_id _).symm

theorem cmp_app_sec (a : Z' ⟶ Z) (g : Z ⟶ B) {k : Z' ⟶ B} (w : a ≫ g = k) {U : B.Opens} {V : Z.Opens} {T : Z'.Opens}
    (h₁ : V ≤ g ⁻¹ᵁ U) (h₂ : T ≤ a ⁻¹ᵁ V) (h : T ≤ k ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((cmp a g w).hom.app E).app T (pullbackSections a _ h₂ (pullbackSections g E h₁ s)) = pullbackSections k E h s := by
  subst w
  exact PullPull.pullbackComp_hom_app a g E h₁ h₂ h s

def tr (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    (Scheme.Modules.pullback a).obj A ⟶ (Scheme.Modules.pullback k).obj E :=
  (Scheme.Modules.pullback a).map u ≫ (cmp a g w).hom.app E

theorem exists_cokerIso_tr (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A : Z.Modules}
    (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    ∃ ψ : (Scheme.Modules.pullback a).obj (cokernel u) ≅ cokernel (tr a w u),
      (Scheme.Modules.pullback a).map (cokernel.π u) ≫ ψ.hom = (cmp a g w).hom.app E ≫ cokernel.π (tr a w u) := by
  refine ⟨PreservesCokernel.iso (Scheme.Modules.pullback a) u ≪≫
    (cokernelCompIsIso ((Scheme.Modules.pullback a).map u) ((cmp a g w).hom.app E)).symm, ?_⟩
  have : (Scheme.Modules.pullback a).map (cokernel.π u) ≫ (PreservesCokernel.iso (Scheme.Modules.pullback a) u).hom =
      cokernel.π _ := by
    rw [← Iso.eq_comp_inv, PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  rw [Iso.trans_hom, reassoc_of% this]
  simp [tr]

theorem tr_good (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A : Z.Modules}
    (u : A ⟶ (Scheme.Modules.pullback g).obj E) [Mono u] (h₁ : IsVB A m) (h₂ : IsVB (cokernel u) r) :
    Mono (tr a w u) ∧ IsVB (cokernel (tr a w u)) r := by
  have := (SubPull.isSubbundle_pullback _ _ a _ _ u m h₁ ⟨inferInstance, r, h₂⟩).mono
  obtain ⟨ψ, -⟩ := exists_cokerIso_tr a w u
  exact ⟨by unfold tr; infer_instance, (h₂.pullback a).of_iso ψ⟩

theorem Same.tr (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {A A' : Z.Modules}
    {u : A ⟶ (Scheme.Modules.pullback g).obj E} {v : A' ⟶ (Scheme.Modules.pullback g).obj E} (h : Same u v) :
    Same (tr a w u) (tr a w v) := (h.pull a).comp _

theorem same_tr_id {g : Z ⟶ B} (w : 𝟙 Z ≫ g = g) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    Same (tr (𝟙 Z) w u) u :=
  ⟨(Scheme.Modules.pullbackId Z).app A, by
    rw [tr, cmp_id]; exact ((Scheme.Modules.pullbackId Z).hom.naturality u).symm⟩

theorem same_tr_tr (b : Z'' ⟶ Z') (a : Z' ⟶ Z) {g : Z ⟶ B} {k : Z' ⟶ B} (w : a ≫ g = k) {l : Z'' ⟶ B} (w₂ : b ≫ k = l)
    {c : Z'' ⟶ Z} (w₁ : b ≫ a = c) (w₃ : c ≫ g = l) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) :
    Same (tr b w₂ (tr a w u)) (tr c w₃ u) :=
  ⟨(cmp b a w₁).app A, by
    simp only [tr, Iso.app_hom, Functor.map_comp, Category.assoc]
    rw [cmp_assoc b a g w w₂ w₁ w₃, cmp_naturality_assoc]⟩

variable (E m r) in

structure Pt (Z : Scheme.{0}) : Type where

  g : Z ⟶ B

  N : Sub ((Scheme.Modules.pullback g).obj E)
  vbN : IsVB N.toMod m
  vb : IsVB (cokernel N.incl) r

def Pt.ofMono (g : Z ⟶ B) {A : Z.Modules} (u : A ⟶ (Scheme.Modules.pullback g).obj E) [Mono u] (h₁ : IsVB A m)
    (h₂ : IsVB (cokernel u) r) : Pt E m r Z :=
  ⟨g, img u, (isVB_of_same (same_img u) h₁ h₂).1, (isVB_of_same (same_img u) h₁ h₂).2⟩

def R (a : Z' ⟶ Z) (x : Pt E m r Z) (y : Pt E m r Z') : Prop :=
  ∃ w : a ≫ x.g = y.g, Same (tr a w x.N.incl) y.N.incl

def Pt.map (a : Z' ⟶ Z) (x : Pt E m r Z) : Pt E m r Z' :=
  haveI := (tr_good a rfl x.N.incl x.vbN x.vb).1
  Pt.ofMono (a ≫ x.g) (tr a rfl x.N.incl) (x.vbN.pullback a) (tr_good a rfl x.N.incl x.vbN x.vb).2

theorem R_map (a : Z' ⟶ Z) (x : Pt E m r Z) : R a x (x.map a) :=
  haveI := (tr_good a rfl x.N.incl x.vbN x.vb).1
  ⟨rfl, (same_img _).symm⟩

theorem R.unique {a : Z' ⟶ Z} {x : Pt E m r Z} {y y' : Pt E m r Z'} (h : R a x y) (h' : R a x y') : y = y' := by
  obtain ⟨g, N, _, _⟩ := y
  obtain ⟨g', N', _, _⟩ := y'
  obtain ⟨w, h⟩ := h
  obtain ⟨w', h'⟩ := h'
  obtain rfl : g = g' := w.symm.trans w'
  obtain rfl : N = N' := sub_ext (h.symm.trans h')
  rfl

theorem map_eq_iff {a : Z' ⟶ Z} {x : Pt E m r Z} {y : Pt E m r Z'} : x.map a = y ↔ R a x y :=
  ⟨fun h => h ▸ R_map a x, (R_map a x).unique⟩

theorem R_id (x : Pt E m r Z) : R (𝟙 Z) x x := ⟨Category.id_comp _, same_tr_id _ _⟩

theorem R.comp {a : Z' ⟶ Z} {b : Z'' ⟶ Z'} {x : Pt E m r Z} {y : Pt E m r Z'} {z : Pt E m r Z''} (h : R a x y)
    (h' : R b y z) : R (b ≫ a) x z := by
  obtain ⟨w, h⟩ := h
  obtain ⟨w', h'⟩ := h'
  have w₃ : (b ≫ a) ≫ x.g = z.g := by rw [Category.assoc, w, w']
  exact ⟨w₃, ((same_tr_tr b a w w' rfl w₃ _).symm.trans (Same.tr b w' h)).trans h'⟩

variable (E m r) in

def fct : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt E m r Z.unop
  map a := TypeCat.ofHom (Pt.map a.unop)
  map_id Z := by
    ext x
    exact map_eq_iff.2 (R_id x)
  map_comp a b := by
    ext x
    exact map_eq_iff.2 ((R_map _ x).comp (R_map _ _))

theorem fct_map (a : Z' ⟶ Z) (x : Pt E m r Z) : (fct E m r).map a.op x = x.map a := rfl

def qs (y : Pt E m r Z) {U : B.Opens} (s : Γ(E, U)) {V : Z.Opens} (h : V ≤ y.g ⁻¹ᵁ U) : Γ(cokernel y.N.incl, V) :=
  (cokernel.π y.N.incl).app V (pullbackSections y.g E h s)

theorem R.exists_iso {a : Z' ⟶ Z} {x : Pt E m r Z} {y : Pt E m r Z'} (H : R a x y) :
    ∃ ψ : (Scheme.Modules.pullback a).obj (cokernel x.N.incl) ≅ cokernel y.N.incl,
      ∀ (U : B.Opens) (s : Γ(E, U)) (V : Z.Opens) (h : V ≤ x.g ⁻¹ᵁ U) (V' : Z'.Opens) (h' : V' ≤ a ⁻¹ᵁ V)
        (h'' : V' ≤ y.g ⁻¹ᵁ U), ψ.hom.app V' (pullbackSections a _ h' (qs x s h)) = qs y s h'' := by
  obtain ⟨w, H⟩ := H
  obtain ⟨ψ, hψ⟩ := exists_cokerIso_tr a w x.N.incl
  obtain ⟨χ, hχ⟩ := exists_cokerIso H
  refine ⟨ψ ≪≫ χ, fun U s V h V' h' h'' => ?_⟩
  rw [qs, qs, ← pullback_map_app_pullbackSections, QCoh.app_app, Iso.trans_hom, reassoc_of% hψ, hχ,
    ← cmp_app_sec a x.g w h h' h'', QCoh.app_app]
  rfl

variable (E m r) in

structure Chart : Type where

  U : B.Opens

  e : Fin m ⊕ Fin r → Γ(E, U)
  he : IsFrame e

variable (c : Chart E m r)

def Gr (y : Pt E m r Z) (h : ⊤ ≤ y.g ⁻¹ᵁ c.U) (α : Fin m → Fin r → Γ(Z, ⊤)) : Prop :=
  IsFrame (fun k => qs y (c.e (.inr k)) h) ∧ ∀ i, qs y (c.e (.inl i)) h = ∑ k, α i k • qs y (c.e (.inr k)) h

theorem R.gr {a : Z' ⟶ Z} {x : Pt E m r Z} {y : Pt E m r Z'} (H : R a x y) {h : ⊤ ≤ x.g ⁻¹ᵁ c.U}
    {α : Fin m → Fin r → Γ(Z, ⊤)} (G : Gr c x h α) : ∃ h', Gr c y h' fun i k => a.appTop (α i k) := by
  obtain ⟨ψ, hψ⟩ := H.exists_iso
  have w : y.g ⁻¹ᵁ c.U = a ⁻¹ᵁ x.g ⁻¹ᵁ c.U := by rw [← H.1, Scheme.Hom.comp_preimage]
  have := x.vb.isQuasicoherent
  have h' : ⊤ ≤ y.g ⁻¹ᵁ c.U := (a.preimage_mono h).trans w.ge
  refine ⟨h', ?_, fun i => ?_⟩
  · rw [← funext fun k => hψ _ (c.e (.inr k)) ⊤ h ⊤ le_rfl h']
    exact (G.1.pullback a).map_iso ψ.hom
  · have e : a.appLE ⊤ ⊤ le_rfl = a.appTop := (a.app_eq_appLE (U := ⊤)).symm
    rw [← hψ _ _ ⊤ h ⊤ le_rfl, G.2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, hψ _ _ _ _ _ _ h', e]

theorem isFrame_pull [E.IsQuasicoherent] (g : Z ⟶ B) {V : Z.Opens} (h : V ≤ g ⁻¹ᵁ c.U) :
    IsFrame fun i => pullbackSections g E h (c.e i) := by
  convert (c.he.pullback g).res h using 2 with i
  exact (res_pullbackSections _ _ _ _ _).symm

theorem Gr.eq [E.IsQuasicoherent] {y y' : Pt E m r Z} (w : y.g = y'.g) {h : ⊤ ≤ y.g ⁻¹ᵁ c.U} {h' : ⊤ ≤ y'.g ⁻¹ᵁ c.U}
    {α : Fin m → Fin r → Γ(Z, ⊤)} (H : Gr c y h α) (H' : Gr c y' h' α) : y = y' := by
  obtain ⟨g, N, _, _⟩ := y
  obtain ⟨g', N', _, _⟩ := y'
  obtain rfl : g = g' := w
  obtain rfl : N = N' := sub_ext (UpperTheory.cokernel_frame_compat_mono Z _ _ _ N.incl N'.incl m r _ α inferInstance inferInstance
    (isFrame_pull c g h) H.1 H.2 H'.1 H'.2)
  rfl

end UpperTheory.Grass
