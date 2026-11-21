import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

noncomputable section

namespace GlobalTheory.DrinLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}}

structure FreeChart (Z : Over S) where

  R : Type
  [ringR : CommRing R]

  t : Sp R ⟶ S

  B : Type
  [ringB : CommRing B]
  [alg : Algebra R B]
  [free : Module.Free R B]
  [fin : Module.Finite R B]

  e : Sp B ≅ pullback Z.hom t

  e_snd : e.hom ≫ pullback.snd Z.hom t = spMap (algebraMap R B)

attribute [instance] FreeChart.ringR FreeChart.ringB FreeChart.alg FreeChart.free FreeChart.fin

def FreeChart.ev {Z : Over S} (c : FreeChart Z) (P : 𝟙_ (Over S) ⟶ Z) : c.B →+* c.R :=
  (Spec.preimage (pullback.lift (c.t ≫ P.left) (𝟙 _)
    (by rw [Category.assoc, Over.w P]; rfl) ≫ c.e.inv)).hom

def IsFinLocFree (Z : Over S) (N : ℕ) : Prop :=
  ∀ x : S, ∃ c : FreeChart Z, IsOpenImmersion c.t ∧ x ∈ Set.range c.t ∧ Module.finrank c.R c.B = N

def IsFullSet (Z : Over S) {J : Type} (P : J → (𝟙_ (Over S) ⟶ Z)) : Prop :=
  Finite J ∧ IsFinLocFree Z (Nat.card J) ∧
    ∀ (c : FreeChart Z) (f : c.B), Algebra.norm c.R f = ∏ᶠ i, c.ev (P i) f

variable {O : Type} [CommRing O]

end GlobalTheory.DrinLev

namespace GlobalTheory.DrinLev
end GlobalTheory.DrinLev
