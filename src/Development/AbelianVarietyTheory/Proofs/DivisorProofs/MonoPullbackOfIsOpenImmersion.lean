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

end GlobalTheory.FlagLocal
