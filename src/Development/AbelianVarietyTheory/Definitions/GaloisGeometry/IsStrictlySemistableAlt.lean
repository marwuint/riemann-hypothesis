import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def push (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : H R n Z →ₗ[R] H R n X where
  toFun x := (Abelian.Ext.mk₀ t).comp (x : HS R (coef R) n Z) (zero_add n)
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _
  map_smul' r _ := Abelian.Ext.comp_smul _ _ _ (ULift.up r : ULift.{1} R)

end Transfer

section Mu

variable (n : ℕ) [NeZero n]

def Mu (A : Type) [CommRing A] : Type := Additive (rootsOfUnity n A)

instance (A : Type) [CommRing A] : AddCommGroup (Mu n A) := inferInstanceAs (AddCommGroup (Additive (rootsOfUnity n A)))

instance (A : Type) [CommRing A] : Module (ZMod n) (Mu n A) :=
  AddCommGroup.zmodModule (fun x => by
    have h : (Additive.toMul (show Additive (rootsOfUnity n A) from x)) ^ n = 1 :=
      Subtype.ext (Additive.toMul (show Additive (rootsOfUnity n A) from x)).2
    exact congrArg Additive.ofMul h)

def Mu.map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Mu n A →ₗ[ZMod n] Mu n B :=
  AddMonoidHom.toZModLinearMap n
    (MonoidHom.toAdditive (restrictRootsOfUnity φ n) : Additive (rootsOfUnity n A) →+ Additive (rootsOfUnity n B))

end Mu

def IsStrictlySemistable {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ}) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.Et

end
