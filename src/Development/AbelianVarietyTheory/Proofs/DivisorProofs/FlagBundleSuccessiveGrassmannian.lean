import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram

noncomputable section

namespace GlobalTheory.OmitGlue

open CategoryTheory Limits AlgebraicGeometry GlobalTheory GlobalTheory.VB GlobalTheory.Vert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Cat

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

private def Le (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ u : A ⟶ B, u ≫ g = f

private def Same (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ e : A ≅ B, e.hom ≫ g = f

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

private theorem Le.refl (f : A ⟶ E) : Le f f := ⟨𝟙 _, Category.id_comp _⟩

private theorem Le.trans (h : Le f g) (h' : Le g f') : Le f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≫ v, Category.assoc ..⟩

private theorem Le.comp (h : Le f g) (t : E ⟶ E') : Le (f ≫ t) (g ≫ t) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (Category.assoc ..).symm⟩

private theorem Same.refl (f : A ⟶ E) : Same f f := ⟨Iso.refl _, Category.id_comp _⟩

private theorem Same.of_eq {f f' : A ⟶ E} (h : f = f') : Same f f' := h ▸ .refl f

private theorem Same.symm (h : Same f g) : Same g f := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.symm, e.inv_hom_id_assoc _⟩

private theorem Same.trans (h : Same f g) (h' : Same g f') : Same f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≪≫ v, Category.assoc ..⟩

private theorem Same.le (h : Same f g) : Le f g := h.elim fun e he => ⟨e.hom, he⟩

private theorem Same.map (h : Same f g) (F : C ⥤ C') : Same (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.mapIso u, (F.map_comp ..).symm⟩

private theorem Same.comp (h : Same f g) (t : E ⟶ E') : Same (f ≫ t) (g ≫ t) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (Category.assoc ..).symm⟩

private theorem same_isIso_comp (u : A ⟶ B) [IsIso u] (g : B ⟶ E) : Same (u ≫ g) g := ⟨asIso u, rfl⟩

private def Ov {P E Q M K : C} (j : P ⟶ E) (q : E ⟶ Q) (μ : M ⟶ E) (κ : K ⟶ Q) : Prop :=
  Le j μ ∧ ∃ g : M ⟶ K, g ≫ κ = μ ≫ q ∧ Epi g

private theorem Ov.map {P E Q M K : C} {j : P ⟶ E} {q : E ⟶ Q} {μ : M ⟶ E} {κ : K ⟶ Q} (h : Ov j q μ κ)
    (F : C ⥤ C') [F.PreservesEpimorphisms] {P' E' Q' : C'} {j' : P' ⟶ E'} {q' : E' ⟶ Q'}
    (β : F.obj E ⟶ E') (χ : F.obj Q ⟶ Q') (h₁ : Le j' (F.map j ≫ β)) (h₂ : β ≫ q' = F.map q ≫ χ) :
    Ov j' q' (F.map μ ≫ β) (F.map κ ≫ χ) := by
  obtain ⟨⟨u, rfl⟩, g, hg, _⟩ := h
  refine ⟨h₁.trans ⟨F.map u, by simp⟩, F.map g, ?_, inferInstance⟩
  rw [← F.map_comp_assoc, hg, Category.assoc, h₂, F.map_comp_assoc]

end Cat

section Ab

variable {C : Type*} [Category C] [Abelian C] {P E Q M K M' K' : C} {j : P ⟶ E} {q : E ⟶ Q}
  {μ : M ⟶ E} {κ : K ⟶ Q} {μ' : M' ⟶ E} {κ' : K' ⟶ Q}

private def Cok (j : P ⟶ E) (q : E ⟶ Q) : Prop :=
  j ≫ q = 0 ∧ Epi q ∧ ∀ (Z : C) (b : E ⟶ Z), j ≫ b = 0 → ∃ a, q ≫ a = b

private theorem Cok.nonempty_iso (h : Cok j q) : Nonempty (cokernel j ≅ Q) := by
  obtain ⟨h₀, _, h₁⟩ := h
  obtain ⟨a, ha⟩ := h₁ _ _ (cokernel.condition j)
  exact ⟨cokernel.desc j q h₀, a, by rw [← cancel_epi (cokernel.π j)]; simp [ha],
    by rw [← cancel_epi q, reassoc_of% ha]; simp⟩

private theorem Cok.exact (h : Cok j q) : (ShortComplex.mk j q h.1).Exact := by
  have := h.2.1
  choose a ha using h.2.2
  exact ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ _ _ (fun b hb => a _ b hb)
    (fun b hb => ha _ b hb) fun b hb m hm => by rw [← cancel_epi q, hm, ha])

private theorem Cok.map {C' : Type*} [Category C'] [Abelian C'] (F : C ⥤ C') [F.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F] (j : P ⟶ E) {E' : C'} (β : F.obj E ≅ E') :
    Cok (F.map j ≫ β.hom) (β.inv ≫ F.map (cokernel.π j)) := by
  have e : F.map (cokernel.π j) = cokernel.π (F.map j) ≫ (PreservesCokernel.iso F j).inv := by
    rw [PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  rw [e]
  refine ⟨by simp [← F.map_comp], inferInstance, fun Z b hb => ⟨(PreservesCokernel.iso F j).hom ≫
    cokernel.desc (F.map j) (β.hom ≫ b) (by simpa using hb), by simp⟩⟩

end Ab

section Bundles

variable {X : Scheme.{0}} {A B E E' S P Q E₁ M K : X.Modules} {a b r : ℕ}

private theorem rank_cokernel {g : B ⟶ E} (hg : IsSubbundle g) (hB : IsVB B b) (hE : IsVB E r) :
    IsVB (cokernel g) (r - b) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨_, s, hs⟩ := hg
  obtain rfl : s = r - b := by
    have := hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk g (cokernel.π _)
      (cokernel.condition _)) b s { exact := ShortComplex.exact_cokernel _ } hB hs).1
    omega
  exact hs x

end Bundles

section Part

variable {X : Scheme.{0}} {A A' E S P Q E₁ : X.Modules} {n i : ℕ}

private def SameFl {r : ℕ} (f f' : Flag E r) : Prop := ∀ l, Same (f.ι l) (f'.ι l)

private theorem SameFl.symm {r : ℕ} {f f' : Flag E r} (h : SameFl f f') : SameFl f' f := fun l => (h l).symm

private theorem SameFl.trans {r : ℕ} {f f' f'' : Flag E r} (h : SameFl f f') (h' : SameFl f' f'') : SameFl f f'' :=
  fun l => (h l).trans (h' l)

private structure Dat (s : S ⟶ P) (j : P ⟶ E) (q : E ⟶ Q) (t : P ⟶ E₁) (n i : ℕ) : Prop where
  hs : IsSubbundle s
  hj : IsSubbundle j
  hq : Cok j q
  ht : Cok s t
  hE : IsVB E n
  hS : IsVB S i
  hP : IsVB P (i + 2)
  le : i + 2 ≤ n

variable {s : S ⟶ P} {j : P ⟶ E} {q : E ⟶ Q} {t : P ⟶ E₁}

private theorem Dat.hQ (D : Dat s j q t n i) : IsVB Q (n - (i + 2)) :=
  (rank_cokernel D.hj D.hP D.hE).of_iso D.hq.nonempty_iso.some

variable (s j q t) in

private def PartAt (fS : Flag S i) (fQ : Flag Q (n - (i + 2))) (l : ℕ) (μ : A ⟶ E) : Prop :=
  (∀ m : Fin (i + 1), (m : ℕ) = l → Same μ (fS.ι m ≫ s ≫ j)) ∧
    ∀ m : Fin (n - (i + 2) + 1), i + 2 + m = l → Ov j q μ (fQ.ι m)

variable (s j t) in

private def MidAt (f₁ : Flag E₁ 2) (μ : A ⟶ E) : Prop := ∃ x : A ⟶ P, x ≫ j = μ ∧ Ov s t x (f₁.ι 1)

variable {fS fS' : Flag S i} {fQ fQ' : Flag Q (n - (i + 2))} {f₁ f₁' : Flag E₁ 2} {l l' : ℕ} {μ : A ⟶ E}
  {μ' : A' ⟶ E}

variable (s j q t) in

private def Glue (fl : Flag E n) (fS : Flag S i) (f₁ : Flag E₁ 2) (fQ : Flag Q (n - (i + 2))) : Prop :=
  ∀ l : Fin (n + 1), PartAt s j q fS fQ l (fl.ι l) ∧ ((l : ℕ) = i + 1 → MidAt s j t f₁ (fl.ι l))

variable {fl fl' : Flag E n}

end Part

section Pull

open GlobalTheory.LineQuot GlobalTheory.CovTest

variable {T T' Y B G : Scheme.{0}}

private def pullTo {π : Y ⟶ B} {E : B.Modules} {r : ℕ} (fl : Flag ((Scheme.Modules.pullback π).obj E) r) (h : T ⟶ Y)
    {g : T ⟶ B} (w : h ≫ π = g) : Flag ((Scheme.Modules.pullback g).obj E) r :=
  (fl.pull h).ofIso ((cmp h π w).app E)

private theorem pullTo_ι {π : Y ⟶ B} {E : B.Modules} {r : ℕ} (fl : Flag ((Scheme.Modules.pullback π).obj E) r) (h : T ⟶ Y)
    {g : T ⟶ B} (w : h ≫ π = g) (l : Fin (r + 1)) :
    (pullTo fl h w).ι l = (Scheme.Modules.pullback h).map (fl.ι l) ≫ (cmp h π w).hom.app E := rfl

private theorem isFlagBundle_iff {π : Y ⟶ B} {ι : Type} {E : ι → B.Modules} {n : ι → ℕ}
    {fl : ∀ a, Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)} : IsFlagBundle π E n fl ↔
    ∀ (T : Scheme.{0}) (g : T ⟶ B) (fl' : ∀ a, Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
      ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, ∀ a, SameFl (pullTo (fl a) g' w) (fl' a) := Iff.rfl

variable {γ : G ⟶ B} {E : B.Modules} {S P : G.Modules} (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E)

private def jk (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g) :
    (Scheme.Modules.pullback k).obj P ⟶ (Scheme.Modules.pullback g).obj E :=
  (Scheme.Modules.pullback k).map j ≫ (cmp k γ w).hom.app E

private def qk (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g) :
    (Scheme.Modules.pullback g).obj E ⟶ (Scheme.Modules.pullback k).obj (cokernel j) :=
  (cmp k γ w).inv.app E ≫ (Scheme.Modules.pullback k).map (cokernel.π j)

variable {s j} {n i : ℕ}

variable {k : T ⟶ G} {g : T ⟶ B} {w : k ≫ γ = g} (h : T' ⟶ T) {k' : T' ⟶ G} {g' : T' ⟶ B} (wk : h ≫ k = k')
  (wg : h ≫ g = g') (w' : k' ≫ γ = g')

@[reassoc] private theorem map_jk : (Scheme.Modules.pullback h).map (jk j k w) ≫ (cmp h g wg).hom.app E =
    (cmp h k wk).hom.app P ≫ jk j k' w' := by
  rw [jk, jk, Functor.map_comp, Category.assoc, cmp_assoc h k γ w wg wk w', cmp_naturality_assoc]

private theorem map_qk : (cmp h g wg).hom.app E ≫ qk j k' w' =
    (Scheme.Modules.pullback h).map (qk j k w) ≫ (cmp h k wk).hom.app _ := by
  rw [← cancel_epi ((Scheme.Modules.pullback h).map ((cmp k γ w).hom.app E)), cmp_assoc_assoc h k γ w wg wk w',
    qk, qk, ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc, cmp_naturality]

variable {fS : Flag ((Scheme.Modules.pullback k).obj S) i}
  {fQ : Flag ((Scheme.Modules.pullback k).obj (cokernel j)) (n - (i + 2))}
  {f₁ : Flag ((Scheme.Modules.pullback k).obj (cokernel s)) 2}

private theorem PartAt.pull {A : T.Modules} {μ : A ⟶ (Scheme.Modules.pullback g).obj E} {l : ℕ}
    (H : PartAt ((Scheme.Modules.pullback k).map s) (jk j k w) (qk j k w) fS fQ l μ) :
    PartAt ((Scheme.Modules.pullback k').map s) (jk j k' w') (qk j k' w') (pullTo fS h wk) (pullTo fQ h wk) l
      ((Scheme.Modules.pullback h).map μ ≫ (cmp h g wg).hom.app E) := by
  refine ⟨fun m hm => (((H.1 m hm).map (Scheme.Modules.pullback h)).comp _).trans (.of_eq ?_), fun m hm => ?_⟩
  · rw [pullTo_ι]
    simp only [Functor.map_comp, Category.assoc]
    rw [map_jk h wk wg w', cmp_naturality_assoc]
  · refine (H.2 m hm).map (Scheme.Modules.pullback h) _ _ ?_ (map_qk h wk wg w')
    rw [map_jk h wk wg w']
    exact (same_isIso_comp _ _).symm.le

private theorem MidAt.pull {A : T.Modules} {μ : A ⟶ (Scheme.Modules.pullback g).obj E}
    (H : MidAt ((Scheme.Modules.pullback k).map s) (jk j k w) ((Scheme.Modules.pullback k).map (cokernel.π s)) f₁ μ) :
    MidAt ((Scheme.Modules.pullback k').map s) (jk j k' w') ((Scheme.Modules.pullback k').map (cokernel.π s))
      (pullTo f₁ h wk) ((Scheme.Modules.pullback h).map μ ≫ (cmp h g wg).hom.app E) := by
  obtain ⟨x, rfl, hx⟩ := H
  refine ⟨(Scheme.Modules.pullback h).map x ≫ (cmp h k wk).hom.app P, ?_,
    hx.map (Scheme.Modules.pullback h) _ _ ?_ (cmp_naturality h k wk _).symm⟩
  · rw [Functor.map_comp, Category.assoc, Category.assoc, map_jk h wk wg w']
  · rw [cmp_naturality]
    exact (same_isIso_comp _ _).symm.le

private theorem Glue.pull {fl : Flag ((Scheme.Modules.pullback g).obj E) n}
    (H : Glue ((Scheme.Modules.pullback k).map s) (jk j k w) (qk j k w)
      ((Scheme.Modules.pullback k).map (cokernel.π s)) fl fS f₁ fQ) :
    Glue ((Scheme.Modules.pullback k').map s) (jk j k' w') (qk j k' w')
      ((Scheme.Modules.pullback k').map (cokernel.π s)) (pullTo fl h wg) (pullTo fS h wk) (pullTo f₁ h wk)
      (pullTo fQ h wk) :=
  fun l => ⟨(H l).1.pull h wk wg w', fun hl => ((H l).2 hl).pull h wk wg w'⟩

end Pull

end GlobalTheory.OmitGlue

end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB
