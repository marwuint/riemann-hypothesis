import Mathlib

namespace ReciprocityTheory.Def

open IsLocalRing Matrix

universe u v w w'

class IsCNL (O : Type u) (A : Type w) [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (maximalIdeal A) A
  localHom : IsLocalHom (algebraMap O A)
  resSurj : Function.Surjective fun x : O => residue A (algebraMap O A x)

attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom

structure Pattern (n : ℕ) where
  rel : Fin n → Fin n → Prop
  refl : ∀ i, rel i i
  trans : ∀ i j l, rel i j → rel j l → rel i l

namespace Pattern

variable {n : ℕ}

def Mem (S : Pattern n) {A : Type*} [Zero A] (X : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ i j, ¬ S.rel i j → X i j = 0

end Pattern

section Lift

variable (O : Type u) [CommRing O] [IsLocalRing O]
variable {G : Type v} [Group G] [TopologicalSpace G] {n : ℕ}

structure IsLift (S : Pattern n) (rbar : G →* GL (Fin n) (ResidueField O))
    {A : Type w} [CommRing A] [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)]
    (ρ : G →* GL (Fin n) A) : Prop where
  cont : ∀ N : ℕ, IsOpen {g : G | ∀ i j, (ρ g).val i j - (1 : Matrix (Fin n) (Fin n) A) i j ∈ maximalIdeal A ^ N}
  red : ∀ g, (ρ g).val.map (residue A) = (rbar g).val.map (ResidueField.map (algebraMap O A))
  mem : ∀ g, S.Mem (ρ g).val

def push {A : Type w} {B : Type w'} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (f : A →ₐ[O] B)
    (ρ : G →* GL (Fin n) A) : G →* GL (Fin n) B :=
  (Matrix.GeneralLinearGroup.map f.toRingHom).comp ρ

end Lift

end ReciprocityTheory.Def
