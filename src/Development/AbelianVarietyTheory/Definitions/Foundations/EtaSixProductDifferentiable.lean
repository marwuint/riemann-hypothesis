import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

def ev (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) : SL(2, ℤ) → ℂ := fun x => (F ∣[k] x) τ

def lead (M : ℕ) (k : ℤ) (F : ℍ → ℂ) : SL(2, ℤ) → Fin M → ℂ := fun x a =>
  (qExpansion (M : ℝ) (F ∣[k] x)).coeff (a : ℕ)

structure Frame (Γ : Subgroup SL(2, ℤ)) (M r : ℕ) where
  wt : Fin r → ℕ
  F : ∀ i, ModularForm Γ (wt i : ℤ)
  odd : ∀ i, Odd (wt i)
  pt : ∀ τ : ℍ, LinearIndependent ℂ (fun i => ev (wt i : ℤ) (F i) τ)
  cusp : LinearIndependent ℂ (fun i => lead M (wt i : ℤ) (F i))

section EtaSix

open Complex Function ModularForm
open scoped Manifold Real

end EtaSix

end GlobalTheory.HeckeFamilyMatrices
