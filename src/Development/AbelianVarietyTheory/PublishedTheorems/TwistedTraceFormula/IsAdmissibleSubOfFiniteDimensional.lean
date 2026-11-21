import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix
open GlobalTheory.SmoothGlob (lieSet)
open scoped ContDiff

namespace GlobalTheory.GKModule

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

@[simp] theorem mem_kFinVec {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H} :
    v ∈ kFinVec ε σ ↔ IsKFin ε σ v := Iff.rfl

theorem isKStableOn_kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinVec ε σ) := by
  rintro g hg v ⟨S, hS, hv, hSK⟩
  exact ⟨S, hS, hSK g hg v hv, hSK⟩

structure IsGKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop where
  smooth : ∀ v ∈ V, SmoothVec (lieSet ε) σ v
  kFin : ∀ v ∈ V, IsKFin ε σ v
  kStable : IsKStableOn ε σ V
  lieStable : ∀ X ∈ lieSet ε, ∀ v ∈ V, dRep σ X v ∈ V

def IsAdmissibleSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop :=
  ∀ Λ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S | S ≤ V ∧ IsKTypeOf ε σ Λ S} : Submodule ℂ H)

def IsGKHom {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (ε : Fin n → Bool) (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁))
    (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) (e : kFinVec ε σ₁ →ₗ[ℂ] kFinVec ε σ₂) : Prop :=
  (∀ k ∈ Kset ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = σ₁ k v → (e w : H₂) = σ₂ k (e v)) ∧
    ∀ X ∈ lieSet ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = dRep σ₁ X v → (e w : H₂) = dRep σ₂ X (e v)

theorem mem_UJset_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  change kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end GlobalTheory.GKModule

namespace GlobalTheory.Published

open GlobalTheory.GKModule

def AdmissibleClosure : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ V : Submodule ℂ H, IsGKSub ε σ V → IsAdmissibleSub ε σ V →
      (∀ g ∈ UJset ε, ∀ w ∈ V.topologicalClosure, σ g w ∈ V.topologicalClosure) ∧
        ∀ w ∈ V.topologicalClosure, IsKFin ε σ w → w ∈ V

def InfinitesimalEquivalence : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [Nontrivial H₁]
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [Nontrivial H₂]
    (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)),
    IsURepOn (UJset ε) σ₁ → IsIrredOn (UJset ε) σ₁ → IsURepOn (UJset ε) σ₂ → IsIrredOn (UJset ε) σ₂ →
    ∀ e : kFinVec ε σ₁ ≃ₗ[ℂ] kFinVec ε σ₂, IsGKHom ε σ₁ σ₂ e.toLinearMap →
      ∃ (U : H₁ ≃ₗᵢ[ℂ] H₂) (c : ℝ), 0 < c ∧ (∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) ∧
        ∀ v : kFinVec ε σ₁, U v = (c : ℂ) • (e v : H₂)

def GKGlobalisation : Prop := AdmissibleClosure ∧ InfinitesimalEquivalence

end GlobalTheory.Published

end
