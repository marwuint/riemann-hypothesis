import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.FlagLocal

variable {X Y S : Scheme.{0}} {A A' A'' E E' : X.Modules}

def Same (u : A ⟶ E) (v : A' ⟶ E) : Prop := ∃ e : A ≅ A', e.hom ≫ v = u

theorem Same.refl (u : A ⟶ E) : Same u u := ⟨Iso.refl _, Category.id_comp _⟩

theorem Same.symm {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) : Same v u :=
  have ⟨e, he⟩ := h
  ⟨e.symm, by rw [← he]; simp⟩

theorem Same.trans {u : A ⟶ E} {v : A' ⟶ E} {w : A'' ⟶ E} (h : Same u v) (h' : Same v w) : Same u w :=
  have ⟨e, he⟩ := h
  have ⟨e', he'⟩ := h'
  ⟨e ≪≫ e', by rw [← he, ← he']; simp⟩

theorem Same.comp {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) (φ : E ⟶ E') : Same (u ≫ φ) (v ≫ φ) :=
  have ⟨e, he⟩ := h
  ⟨e, by rw [← he, Category.assoc]⟩

theorem Same.pull {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) (f : Y ⟶ X) :
    Same ((Scheme.Modules.pullback f).map u) ((Scheme.Modules.pullback f).map v) :=
  have ⟨e, he⟩ := h
  ⟨(Scheme.Modules.pullback f).mapIso e, by rw [← he]; simp⟩

theorem same_of_le_le {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v] (f : A ⟶ A') (g : A' ⟶ A)
    (hf : f ≫ v = u) (hg : g ≫ u = v) : Same u v :=
  ⟨⟨f, g, by rw [← cancel_mono u, Category.assoc, hg, hf, Category.id_comp],
    by rw [← cancel_mono v, Category.assoc, hf, hg, Category.id_comp]⟩, hf⟩

theorem cokernel_app_eq_zero_iff (v : A ⟶ E) [Mono v] (V : X.Opens) (t : Γ(E, V)) :
    (cokernel.π v).app V t = 0 ↔ ∃ m, v.app V m = t :=
  QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel v) V t

theorem exists_fac_of_sections (u : A ⟶ E) (v : A' ⟶ E) [Mono v]
    (h : ∀ (V : X.Opens) (s : Γ(A, V)), ∃ m, v.app V m = u.app V s) : ∃ f : A ⟶ A', f ≫ v = u := by
  have : u ≫ cokernel.π v = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext s
    exact (cokernel_app_eq_zero_iff v V _).2 (h V s)
  exact ⟨Abelian.monoLift v u this, Abelian.monoLift_comp _ _ _⟩

theorem same_of_range {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v]
    (h : ∀ V : X.Opens, Set.range (u.app V) = Set.range (v.app V)) : Same u v := by
  obtain ⟨f, hf⟩ := exists_fac_of_sections u v fun V s => (h V).le ⟨s, rfl⟩
  obtain ⟨g, hg⟩ := exists_fac_of_sections v u fun V s => (h V).ge ⟨s, rfl⟩
  exact same_of_le_le f g hf hg

theorem bijective_pullbackSections (a : Y ⟶ X) [IsOpenImmersion a] (E : X.Modules) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) :
    Function.Bijective (pullbackSections a E hW.le) := by
  subst hW
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction a) E
  have h1 : Function.Bijective (E.presheaf.map (homOfLE (a.image_preimage_le V)).op) :=
    QCoh.res_bijective_of_eq E _ (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_eq_right.2 hV)
  have h2 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback a).hom.app E).app (a ⁻¹ᵁ V))
  convert h2.comp h1 using 1
  funext s
  exact (resM_self _ _).trans congr(($e).app V s).symm

theorem mono_pullback_of_isOpenImmersion (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) [Mono v] :
    Mono ((Scheme.Modules.pullback a).map v) := by
  refine QCoh.mono_of_locally_app_injective _ fun W _ hx => ⟨W, hx, le_rfl, fun s t h => ?_⟩
  have hW := (a.preimage_image_eq W).symm
  have hV := a.image_le_opensRange W
  obtain ⟨s, rfl⟩ := (bijective_pullbackSections a A hV hW).2 s
  obtain ⟨t, rfl⟩ := (bijective_pullbackSections a A hV hW).2 t
  rw [pullback_map_app_pullbackSections, pullback_map_app_pullbackSections] at h
  rw [QCoh.injective_app_of_mono v _ ((bijective_pullbackSections a E hV hW).1 h)]

end GlobalTheory.FlagLocal
