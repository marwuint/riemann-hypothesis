import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EDual

abbrev pt (k : Type) [Field k] : Scheme.{0} := Spec (CommRingCat.of k)

abbrev ptMap {k : Type} [Field k] (σ : k ≃+* k) : pt k ⟶ pt k := Spec.map (CommRingCat.ofHom σ.toRingHom)

structure SP (k : Type) [Field k] (d : ℕ) where
  X : Scheme.{0}
  p : X ⟶ pt k
  proper : IsProper p
  smooth : SmoothOfRelativeDimension d p

structure Cpt (k : Type) [Field k] (d : ℕ) where
  X : Scheme.{0}
  Z : Scheme.{0}
  U : Scheme.{0}
  p : X ⟶ pt k
  ι : Z ⟶ X
  j : U ⟶ X
  proper : IsProper p
  closed : IsClosedImmersion ι
  opn : IsOpenImmersion j
  compl : IsCompl (Set.range ι) (Set.range j)
  smooth : SmoothOfRelativeDimension d (j ≫ p)

def Cpt.Q {k : Type} [Field k] {d : ℕ} (C : Cpt k d) : Spc := pushout (sch.map C.ι) (sch.map (C.ι ≫ C.p))

def Cpt.q {k : Type} [Field k] {d : ℕ} (C : Cpt k d) : C.Q ⟶ sch.obj (pt k) :=
  pushout.desc (sch.map C.p) (𝟙 _) (by rw [Category.comp_id, Functor.map_comp])

structure Cpt.Hom {k : Type} [Field k] {d : ℕ} (C' C : Cpt k d) where
  σ : k ≃+* k
  f : C'.X ⟶ C.X
  z : C'.Z ⟶ C.Z
  u : C'.U ⟶ C.U
  hp : f ≫ C.p = C'.p ≫ ptMap σ
  hz : C'.ι ≫ f = z ≫ C.ι
  hu : C'.j ≫ f = u ≫ C.j

def Cpt.Hom.Q {k : Type} [Field k] {d : ℕ} {C' C : Cpt k d} (φ : Cpt.Hom C' C) : C'.Q ⟶ C.Q :=
  pushout.map _ _ _ _ (sch.map φ.f) (sch.map (ptMap φ.σ)) (sch.map φ.z)
    (by rw [← Functor.map_comp, ← Functor.map_comp, φ.hz])
    (by rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, ← φ.hp, ← Category.assoc, φ.hz, Category.assoc])

end LateralTheory.EDual
end
