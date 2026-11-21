import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Raynaud

section Formal

variable {R : Type} [CommRing R] (I : Ideal R)

def IsFormalIso (G Gt : Over (Sp R)) [GrpObj G] [GrpObj Gt]
    (ψ : ∀ e : ℕ, (thickObj R I e G).left ⟶ Gt.left) : Prop :=
  (∀ e, IsGrpPullback (thickObj R I e G) Gt (thick R I e) (ψ e)) ∧ ∀ e, thickMap R I e G ≫ ψ (e + 1) = ψ e

def IsExtension (G Gt : Over (Sp R)) [GrpObj G] [GrpObj Gt]
    (ψ : ∀ e : ℕ, (thickObj R I e G).left ⟶ Gt.left) : Prop :=
  IsSemiAbelian Gt ∧
    (∃ (X : Type) (_ : AddCommGroup X), Module.Free ℤ X ∧ Module.Finite ℤ X ∧ Nonempty (UU.TQ Gt X)) ∧
    IsFormalIso I G Gt ψ

variable {I}

end Formal

section Parts

variable {S : Scheme.{0}}

def LiesIn {H G : Over S} (j : H ⟶ G) {Y : Scheme.{0}} (x : Y ⟶ G.left) : Prop :=
  ∃ h : Y ⟶ H.left, h ≫ j.left = x

structure IsFiniteFlatSubgroup {H G : Over S} [GrpObj G] (n : ℕ) (j : H ⟶ G) : Prop where
  closed : IsClosedImmersion j.left
  finite : IsFinite H.hom
  flat : Flat H.hom
  one_mem : LiesIn j (η[G]).left
  mul_mem : ∀ (Y : Over S) (a b : Y ⟶ H), LiesIn j ((a ≫ j) * (b ≫ j)).left
  pow_eq_one : j ^ n = 1

variable {V : Type} [CommRing V]

def IsFinitePart {H G : Over (Sp V)} [GrpObj G] (n : ℕ) (j : H ⟶ G) : Prop :=
  IsFiniteFlatSubgroup n j ∧ ∃ (Ω : Type) (_ : Field Ω) (p : V →+* Ω), IsLocalHom p ∧
    ∀ (Y : Over (Sp Ω)) (y : Y ⟶ (Over.pullback (spMap p)).obj G),
      LiesIn j (y.left ≫ pullback.fst G.hom (spMap p)) ↔ y ^ n = 1

def IsTorusPart {H G : Over (Sp V)} [GrpObj G] (n : ℕ) (j : H ⟶ G) : Prop :=
  IsFiniteFlatSubgroup n j ∧ ∃ (Ω : Type) (_ : Field Ω) (p : V →+* Ω), IsLocalHom p ∧
    ∃ E : TorusExtension ((Over.pullback (spMap p)).obj G),
      ∀ (Y : Over (Sp Ω)) (y : Y ⟶ (Over.pullback (spMap p)).obj G),
        LiesIn j (y.left ≫ pullback.fst G.hom (spMap p)) ↔ y ^ n = 1 ∧ ∃ t, t ≫ E.i = y

def PairsToOne {A A' : Over S} [GrpObj A] [GrpObj A'] (P : LB (A ⊗ A').left) (n : ℕ) {T : Over S}
    (x : T ⟶ A) (y : T ⟶ A') : Prop :=
  WeilIs (A ⊗ A') P (n : ℤ) (lift x 1) (lift 1 y) 1

theorem pow_eq_one_iff_of_isGrpPullback {S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {Y : Over S'} (y : Y ⟶ G') (n : ℕ) :
    pushPt h.1.w y ^ n = 1 ↔ y ^ n = 1 := by
  let m : (Y ⟶ G') →* (Over.mk (Y.hom ≫ f) ⟶ G) := MonoidHom.mk' (fun z => pushPt h.1.w z) fun a b =>
    Over.OverMorphism.ext (h.2 Y a b _ _ rfl rfl).symm
  have hm : Function.Injective m := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  show m y ^ n = 1 ↔ _
  rw [← map_pow, map_eq_one_iff m hm]

end Parts

end GlobalTheory.Raynaud

namespace GlobalTheory.Published

open GlobalTheory.Raynaud IsLocalRing

def RaynaudExtension.Exists : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) →
      Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) →
      ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (ψ : ∀ e : ℕ, (thickObj R (maximalIdeal R) e G).left ⟶ Gt.left),
        IsExtension (maximalIdeal R) G Gt ψ

def RaynaudExtension.Functorial : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G G' Gt Gt' : Over (Sp R)) [GrpObj G] [GrpObj G'] [GrpObj Gt] [GrpObj Gt'],
      IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) →
      IsSemiAbelian G' → IsProper (pullback.snd G'.hom (jK R)) →
    ∀ (ψ : ∀ e : ℕ, (thickObj R (maximalIdeal R) e G).left ⟶ Gt.left)
      (ψ' : ∀ e : ℕ, (thickObj R (maximalIdeal R) e G').left ⟶ Gt'.left),
      IsExtension (maximalIdeal R) G Gt ψ → IsExtension (maximalIdeal R) G' Gt' ψ' →
    ∀ f : G ⟶ G', IsMonHom f → ∃! ft : Gt ⟶ Gt', IsMonHom ft ∧
      ∀ e, ψ e ≫ ft.left = ((Over.pullback (thick R (maximalIdeal R) e)).map f).left ≫ ψ' e

def GrothendieckOrthogonality : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [HenselianLocalRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (G G' : Over (Sp V)) [GrpObj G] [GrpObj G'],
    IsSemiAbelian G → IsSemiAbelian G' →
    ∀ (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G'.left),
      IsAbelianScheme A → IsAbelianScheme A' →
      IsGrpPullback A G (spMap (algebraMap V K)) φ → IsGrpPullback A' G' (spMap (algebraMap V K)) φ' →
    ∀ P : LB (A ⊗ A').left, AbDual.IsDual A A' P →
    ∀ (l r : ℕ), l.Prime → (l : K) ≠ 0 →
    ∀ (H H' : Over (Sp V)) (j : H ⟶ G) (j' : H' ⟶ G'), IsTorusPart (l ^ r) j → IsFinitePart (l ^ r) j' →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω],
      (∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, x ^ l ^ r = 1 →
        (LiesIn j (x.left ≫ φ) ↔
          ∀ y : Over.mk (spMap (algebraMap K Ω)) ⟶ A', LiesIn j' (y.left ≫ φ') → PairsToOne P (l ^ r) x y)) ∧
      ∀ y : Over.mk (spMap (algebraMap K Ω)) ⟶ A', y ^ l ^ r = 1 →
        (LiesIn j' (y.left ≫ φ') ↔
          ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, LiesIn j (x.left ≫ φ) → PairsToOne P (l ^ r) x y)

def RaynaudExtension : Prop :=
  RaynaudExtension.Exists ∧ RaynaudExtension.Functorial ∧ GrothendieckOrthogonality

end GlobalTheory.Published
