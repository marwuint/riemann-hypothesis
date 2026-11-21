import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ]

def IsIrr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))

def centralIdem [Fintype Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) :
    MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ γ⁻¹))

theorem zIdem_eq_centralIdem [Fintype Γ] (τ : FDRep ℂ Γ) : zIdem τ = centralIdem τ.ρ := rfl

open Classical in

def ip [Fintype Γ] (S : Set Γ) (a b : Γ → ℂ) : ℂ :=
  (S.ncard : ℂ)⁻¹ * ∑ g, if g ∈ S then a g⁻¹ * b g else 0

def cj (x : Γ) (B : Subgroup Γ) : Subgroup Γ := B.comap (MulAut.conj x).toMonoidHom

theorem mem_cj {x h : Γ} {B : Subgroup Γ} : h ∈ cj x B ↔ x * h * x⁻¹ ∈ B := Iff.rfl

end Gen

section GeneralLinearIntegers

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

abbrev IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ

def glReindex {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β) :
    GL α K ≃* GL β K := glEquiv K e

omit [Fintype K] [DecidableEq K] in
theorem glReindex_val {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (g : GL α K) : ((glReindex K e g : GL β K) : Matrix β β K) = (g : Matrix α α K).submatrix e.symm e.symm := rfl

def CuspIso {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) : Prop :=
  ∃ (e : α ≃ β) (φ : lam ≃ₗ[ℂ] mu), ∀ g x, φ (lam.ρ g x) = mu.ρ (glReindex K e g) (φ x)

variable {K} in

def reRep {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (τ : FDRep ℂ (GL α K)) : FDRep ℂ (GL β K) := transp e τ

instance HC.finiteDimensional_hcSpace {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) : FiniteDimensional ℂ (hcSpace K b lam) := by
  have : FiniteDimensional ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c))
  infer_instance

variable {K}

variable (K) in

def pm {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) : GL ι K :=
  (Matrix.permMatrixHom (n := ι) (R := K)).toHomUnits σ

variable (K) in

def patSet {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) : Set (GL ι K) :=
  {u | ∀ i j, (i = j → (u : Matrix ι ι K) i j = 1) ∧ (i ≠ j → ¬ Φ i j → (u : Matrix ι ι K) i j = 0)}

def patChar {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (u : GL ι K) : ℂ :=
  ψ₀ (∑ i, ∑ j, E i j * (u : Matrix ι ι K) i j)

open Classical in

def wh {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E : ι → ι → K) (ψ₀ : AddChar K ℂ)
    (χ : GL ι K → ℂ) : ℂ :=
  ((patSet K Φ).ncard : ℂ)⁻¹ * ∑ u, if u ∈ patSet K Φ then (patChar E ψ₀ u)⁻¹ * χ u else 0

def IsPat {ι : Type} (Φ : ι → ι → Prop) : Prop := (∀ i, ¬ Φ i i) ∧ ∀ i j k, Φ i j → Φ j k → Φ i k

variable (K) in

def cutE (N k : ℕ) (i j : Fin N) : K := if (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k then 1 else 0

variable (K) in

def jE (N kk s : ℕ) (i j : Fin N) : K :=
  if ((j : ℕ) = i + 1 ∧ ((j : ℕ) < s ∨ (s ≤ (i : ℕ) ∧ (j : ℕ) < s + kk) ∨ s + kk ≤ (i : ℕ))) ∨
    ((i : ℕ) + 1 = s ∧ (j : ℕ) = s + kk) then 1 else 0

end GeneralLinearIntegers

namespace Lq

end Lq

end ReciprocityTheory.Ty.Fin
