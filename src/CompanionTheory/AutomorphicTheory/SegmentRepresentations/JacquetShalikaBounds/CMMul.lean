import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace CompanionTheory.JacquetShalikaLocal

variable {F : Type} [Field F] {n : ℕ}

def inP (m : ℕ) (g : GL (Fin n) F) : Prop :=
  (∀ i j : Fin n, m ≤ (i : ℕ) → g i j = (1 : Matrix (Fin n) (Fin n) F) i j) ∧
    ∀ i j : Fin n, m < (j : ℕ) → g i j = (1 : Matrix (Fin n) (Fin n) F) i j

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def inU (m : ℕ) (g : GL (Fin n) F) : Prop :=
  g ∈ unipotent F n ∧ ∀ i j : Fin n, (j : ℕ) ≤ m → g i j = (1 : Matrix (Fin n) (Fin n) F) i j

def Div {ι : Type} (c : ℕ) (A : Matrix ι ι F) : Prop := ∀ i j, ∃ y ∈ 𝒪[F], A i j = (uniformizer F : F) ^ c * y

variable (F) in

def lat (m M : ℕ) : Set (Fin m → F) := {x | ∀ i, (uniformizer F : F) ^ M * x i ∈ 𝒪[F]}

def PsiOK (ψ : AddChar F ℂ) : Prop :=
  (∀ x ∈ 𝒪[F], ψ x = 1) ∧ (∃ x : F, (uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ x ≠ 1) ∧ ∀ x, ‖ψ x‖ = 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure Inv (ρ : Representation ℂ (GL (Fin n) F) V) (ψ : AddChar F ℂ) (l : V →ₗ[ℂ] ℂ) (m : ℕ)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  herm : ∀ u u', starRingEnd ℂ (B u u') = B u' u
  psd : ∀ u, 0 ≤ (B u u).re
  null : ∀ u, B u u = 0 → l u = 0
  quasi : ∀ g, inP m g → ∀ u u', B (ρ g u) (ρ g u') =
    (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - m) * B u u'
  equi : ∀ g, inU m g → ∀ u u', B u' (ρ g u) = Whittaker.psiN ψ g * B u' u

variable [MeasurableSpace F]

end CompanionTheory.JacquetShalikaLocal

end
