import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4.CurveCut

open LateralTheory.E.E4

def LeafMV : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens), U ⊔ V = ⊤ →
  ∀ n : ℤ, ∃ δ : H R (sch.obj (U ⊓ V).toScheme) F n →+ H R (sch.obj X) F (n + 1),
    ∀ x : H R (sch.obj X) F (n + 1),
      (pull R (sch.map U.ι) F (n + 1) x = 0 ∧ pull R (sch.map V.ι) F (n + 1) x = 0) ↔ x ∈ δ.range

def isoH (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (e : X ≅ Y) (n : ℤ) :
    H R (sch.obj Y) F n ≃ H R (sch.obj X) F n where
  toFun := pull R (sch.map e.hom) F n
  invFun := pull R (sch.map e.inv) F n
  left_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  right_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem finite_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Finite (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Finite (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Finite (H R (sch.obj V.toScheme) F (n + 1))) :
    Finite (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  let φ := (pull R (sch.map U.ι) F (n + 1)).prod (pull R (sch.map V.ι) F (n + 1))
  have hker : φ.ker = δ.range := by
    ext x
    rw [← hδ x, AddMonoidHom.mem_ker]
    simp [φ, Prod.ext_iff]
  have : Finite φ.ker := by
    rw [hker]
    exact Set.finite_range δ |>.to_subtype
  have : Finite (H R (sch.obj X) F (n + 1) ⧸ φ.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_addSubgroup_quotient φ.ker

theorem subsingleton_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Subsingleton (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Subsingleton (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Subsingleton (H R (sch.obj V.toScheme) F (n + 1))) :
    Subsingleton (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj X) F (n + 1), z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hδ z).1 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  rw [hx x, hx y]

end LateralTheory.E.E4.CurveCut
