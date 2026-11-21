import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

def epsHom (f : R →+* R') (c : R') : DualNumber R →+* DualNumber R' where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (c * f x.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [mul_add]
  map_mul' x y := by
    ext
    · simp
    · simp
      ring

@[simp] lemma epsHom_fst (f : R →+* R') (c : R') (x : DualNumber R) :
    (epsHom f c x).fst = f x.fst := by simp [epsHom]

@[simp] lemma epsHom_snd (f : R →+* R') (c : R') (x : DualNumber R) :
    (epsHom f c x).snd = c * f x.snd := by simp [epsHom]

variable (R) in

def epsRed : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom

variable (R) in

abbrev SpEps : Over (Sp R) := Over.mk (spMap (algebraMap R (DualNumber R)))

variable (R) in

def epsZero : 𝟙_ (Over (Sp R)) ⟶ SpEps R :=
  Over.homMk (spMap (epsRed R)) (by
    change spMap (epsRed R) ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsRed R).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext a; simp [epsRed, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, CommRingCat.ofHom_id, Spec.map_id])

def epsScale (c : R) : SpEps R ⟶ SpEps R :=
  Over.homMk (spMap (epsHom (RingHom.id R) c)) (by
    change spMap (epsHom (RingHom.id R) c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsHom (RingHom.id R) c).comp (algebraMap R (DualNumber R)) =
        algebraMap R (DualNumber R) := by
      ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this])

lemma epsZero_scale (c : R) : epsZero R ≫ epsScale c = epsZero R := by
  ext1
  change spMap (epsRed R) ≫ spMap (epsHom (RingHom.id R) c) = spMap (epsRed R)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (epsRed R).comp (epsHom (RingHom.id R) c) = epsRed R := by
    refine RingHom.ext fun x => ?_
    simp [epsRed]
  rw [this]

end Dual

section Lie

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]

def lieSub : Subgroup (SpEps R ⟶ G) where
  carrier := {v | epsZero R ≫ v = η[G]}
  one_mem' := by
    change epsZero R ≫ (1 : SpEps R ⟶ G) = η[G]
    rw [comp_one, Hom.one_def, toUnit_unit, Category.id_comp]
  mul_mem' := by
    intro a b ha hb
    change epsZero R ≫ (a * b) = η[G]
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [comp_mul, show epsZero R ≫ a = η[G] from ha, show epsZero R ≫ b = η[G] from hb, h1, _root_.mul_one]
  inv_mem' := by
    intro a ha
    change epsZero R ≫ a⁻¹ = η[G]
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [GrpObj.comp_inv, show epsZero R ≫ a = η[G] from ha, h1, inv_one]

abbrev Tan : Type := ↥(lieSub G)

variable {G}

def Tan.smul (c : R) (v : Tan G) : Tan G :=
  ⟨epsScale c ≫ v.1, by
    change epsZero R ≫ epsScale c ≫ v.1 = η[G]
    rw [← Category.assoc, epsZero_scale]
    exact v.2⟩

def linComb {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) : Tan G :=
  (List.ofFn fun i => Tan.smul (c i) (v i)).prod

def IsLieBasis {n : ℕ} (v : Fin n → Tan G) : Prop :=
  Function.Bijective fun c : Fin n → R => linComb c v

end Lie

section Input

def NonzeroOnFibres {S : Scheme.{0}} (A : Over S) {L : LB A.left} (s : LB.Sec L) : Prop :=
  ∀ y : S, ∃ x : A.left, A.hom x = y ∧ x ∈ nonzeroLocus s

structure KeyInput (R : Type) [CommRing R] where

  P : PolAV (Sp R)
  dim_pos : 1 ≤ P.g

  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen

  th : LB.Sec P.L
  th_ne : NonzeroOnFibres P.A th

  b : Fin P.g → Tan P.A
  b_basis : IsLieBasis b

variable {R R' : Type} [CommRing R] [CommRing R']

end Input

end GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence
