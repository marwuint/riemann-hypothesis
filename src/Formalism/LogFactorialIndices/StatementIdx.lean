import Mathlib

noncomputable section

namespace Formalism.LatticeIndexTer

open Module
open scoped Pointwise

section Defs

variable (O K X : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup X] [Module K X]
  [Module O X]

def IsLat (A : Submodule O X) : Prop := A.FG ∧ Submodule.span K (A : Set X) = ⊤

end Defs

section Defs2

variable (O X : Type) [CommRing O] [AddCommGroup X] [Module O X]

def qlen (A B : Submodule O X) : ℕ∞ := Module.length O (A ⧸ B.comap A.subtype)

def idx (A B : Submodule O X) : ℤ := ((qlen O X A B).toNat : ℤ) - ((qlen O X B A).toNat : ℤ)

end Defs2

def LatFinite : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B : Submodule O X), IsLat O K X A → IsLat O K X B → qlen O X A B ≠ ⊤

def LatBasis : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (A : Submodule O X), IsLat O K X A →
      ∃ b : Basis (Fin (finrank K X)) K X, A = Submodule.span O (Set.range b)

def IdxAdd : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B C : Submodule O X), IsLat O K X A → IsLat O K X B → IsLat O K X C →
      idx O X A C = idx O X A B + idx O X B C

def IdxDet : Prop :=
  ∀ (O K X Y ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
    (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) (a b : O), a ≠ 0 → b ≠ 0 →
    algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b →
      idx O Y (Submodule.span O (Set.range bY))
          ((Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O)) =
        ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) - ((IsDiscreteValuationRing.addVal O b).toNat : ℤ)

def IdxScale : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ → ∀ (s : ℤ) (N : Submodule O X), IsLat O K X N →
      idx O X N (N.map ((((algebraMap O K ϖ) ^ (-s)) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) =
        -s * (finrank K X : ℤ)

end Formalism.LatticeIndexTer
