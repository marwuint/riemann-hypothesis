import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

structure Near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) where

  U : Over (Sp R)

  smooth : Smooth U.hom

  separated : IsSeparated U.hom

  quasiCompact : QuasiCompact U.hom

  u : pullback U.hom π ⟶ G.left

  isOpen : IsOpenImmersion u

  u_over : u ≫ G.hom = pullback.snd U.hom π

  all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ Set.range u

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def Near.Pt (N : Near π G) {T : Scheme.{0}} (s : T ⟶ S) (a : T ⟶ N.U.left) (x : T ⟶ G.left) : Prop :=
  ∃ x₀ : T ⟶ pullback N.U.hom π, x₀ ≫ pullback.fst _ _ = a ∧ x₀ ≫ pullback.snd _ _ = s ∧ x₀ ≫ N.u = x

def Near.Law [GrpObj G] (N : Near π G) : Prop :=
  ∃ (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left),
    (∀ z : (N.U ⊗ N.U).left, (N.U ⊗ N.U).hom z = closedPoint R → z ∈ V) ∧ m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom ∧
    ∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G),
      N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left →
      N.Pt s (v ≫ m) (x * y).left

def Near.Datum [GrpObj G] (N : Near π G)
    (φ : (Over.pullback (pullback.fst π π)).obj G ≅ (Over.pullback (pullback.snd π π)).obj G) : Prop :=
  IsMonHom φ.hom ∧ ∀ (T : Scheme.{0}) (a : T ⟶ N.U.left) (x : T ⟶ ((Over.pullback (pullback.fst π π)).obj G).left),
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.fst π π) a (x ≫ pullback.fst G.hom (pullback.fst π π)) →
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.snd π π) a
      (x ≫ φ.hom.left ≫ pullback.fst G.hom (pullback.snd π π))

end

def Gal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Subgroup (R' ≃+* R') where
  carrier := {σ | ∀ r, σ (ρ r) = ρ r}
  mul_mem' := fun {a b} ha hb r => by rw [RingAut.mul_apply, hb r, ha r]
  one_mem' := fun _ => rfl
  inv_mem' := fun {a} ha r => by
    have := congrArg a.symm (ha r)
    rw [RingEquiv.symm_apply_apply] at this
    exact this.symm

def Gal.hom {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} (σ : Gal ρ) : R' →+* R' := σ.1.toRingHom

def PullOver {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg ρ D D') (h : IsPullDeg s D' D') : Prop :=
  (∀ x, h.xe x = x) ∧ ∀ (b : D'.P.A.left ⟶ D.P.A.left) (c : D'.P.A.left ⟶ D'.P.A.left),
    b = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) → c = h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) → c ≫ b = b

def IsGal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Prop :=
  Finite (Gal ρ) ∧ ∀ x : R', (∀ σ ∈ Gal ρ, σ x = x) → x ∈ ρ.range

structure GalAct {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R')
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') where

  act : Gal ρ → (G'.left ⟶ G'.left)

  cart : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)

  act_one : act 1 = 𝟙 _

  act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ

  unif : ∀ σ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
    (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
    bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = act σ ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

end GlobalTheory.Mum
