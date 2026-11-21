import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

section Abstract

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

def IsFrame (X : Submodule F Y) (a : Fin c → Y) : Prop :=
  LinearIndependent F a ∧ IsCompl X (Submodule.span F (Set.range a))

def flag (X : Submodule F Y) (a : Fin c → Y) (i : Fin c) : Submodule F Y :=
  X ⊔ Submodule.span F (a '' {l | l < i})

def IsUnip (X : Submodule F Y) (a : Fin c → Y) (n : Y ≃ₗ[F] Y) : Prop :=
  (∀ x ∈ X, n x = x) ∧ (∀ i : Fin c, i.1 = 0 → n (a i) = a i) ∧ ∀ i : Fin c, n (a i) - a i ∈ flag X a i

def IsExtOf (X : Submodule F Y) (a : Fin c → Y) (γ : X ≃ₗ[F] X) (g : Y ≃ₗ[F] Y) : Prop :=
  (∀ x : X, g x = (γ x : Y)) ∧ ∀ i, g (a i) = a i

def IsSemidirect (X : Submodule F Y) (a : Fin c → Y) (r : Y ≃ₗ[F] Y) : Prop :=
  ∃ (γ : X ≃ₗ[F] X) (g n : Y ≃ₗ[F] Y), IsExtOf X a γ g ∧ IsUnip X a n ∧ r = g * n

variable {O : Type} [CommRing O] [Algebra O F] [Module O Y] [IsScalarTower O F Y]

def moveBy (r : Y ≃ₗ[F] Y) (Λ : Submodule O Y) : Submodule O Y :=
  Λ.map (r.toLinearMap.restrictScalars O)

def normalForm (F : Type) [Field F] [Module F Y] [Algebra O F] (q : O) (M : Submodule O Y) (a : Fin c → Y)
    (e : Fin c → ℤ) (z : Y) : Submodule O Y :=
  M ⊔ ⨆ i : Fin c, Submodule.span O {(algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)}

def inY (X : Submodule F Y) (L : Submodule O X) : Submodule O Y :=
  L.map (X.subtype.restrictScalars O)

end Abstract

def LatticeNormalForm : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (L : Submodule O X), Submodule.IsLattice F L →
    ∀ (Λ : Submodule O Y), Submodule.IsLattice F Λ →
      ∃ (r : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsSemidirect X a r ∧ z ∈ X ∧
        moveBy r Λ = normalForm F q (inY X L) a e z

def LatticeNormalFormUnip : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (Λ : Submodule O Y), Submodule.IsLattice F Λ →
      ∃ (n : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsUnip X a n ∧ z ∈ X ∧
        moveBy n Λ = normalForm F q (Λ ⊓ X.restrictScalars O) a e z

open Formalism.L2.Col in

def LatticeNormalFormCoord : Prop :=
  ∀ (O F : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    (q : O), Irreducible q →
    ∀ (n c : ℕ) (L : Submodule O (Fin n → F)), Submodule.IsLattice F L →
    ∀ (Λ : Submodule O (Fin (n + c) → F)), Submodule.IsLattice F Λ →
      ∃ r ∈ Loc.R1 F n c, ∃ (e : Fin c → ℤ) (z : Fin n → F),
        moveBy r Λ = normalForm F q (L.map ((Loc.inX F n c).restrictScalars O))
          (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) e (Loc.inX F n c z)

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect
