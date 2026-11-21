import Mathlib

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace CompanionTheory.KM

variable (k : Type) [Field k] [Fintype k] (kb : Type) [Field kb] [IsAlgClosed kb] [Algebra k kb]

abbrev Sk : Scheme := Spec (CommRingCat.of k)

structure Var where
  Y : Scheme
  s : Y ⟶ Sk k
  smooth : Smooth s
  proper : IsProper s

variable {k}

structure Corr (Y : Var k) where
  C : Scheme
  c₁ : C ⟶ Y.Y
  c₂ : C ⟶ Y.Y
  base : c₁ ≫ Y.s = c₂ ≫ Y.s
  fin₁ : IsFinite c₁
  fin₂ : IsFinite c₂
  et₁ : Etale c₁
  et₂ : Etale c₂

structure CohModel (F : Type) [Field F] where

  H : Var k → ℕ → Type
  [acg : ∀ Y i, AddCommGroup (H Y i)]
  [mod : ∀ Y i, Module F (H Y i)]
  [fd : ∀ Y i, FiniteDimensional F (H Y i)]
  top : Var k → ℕ
  vanish : ∀ Y i, top Y < i → Subsingleton (H Y i)
  frob : ∀ Y i, H Y i →ₗ[F] H Y i
  act : ∀ {Y : Var k}, Corr Y → ∀ i, H Y i →ₗ[F] H Y i
  comm : ∀ {Y : Var k} (c : Corr Y) i, act c i ∘ₗ frob Y i = frob Y i ∘ₗ act c i

attribute [instance] CohModel.acg CohModel.mod CohModel.fd

variable {F : Type} [Field F] {E : Type} [Field E] [CharZero E]

end CompanionTheory.KM
