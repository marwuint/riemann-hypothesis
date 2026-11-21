import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.DivPassage

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage2

open Formalism.L2.Indef Formalism.L2.GlobalTheoryTheory.DivPassage

section Proj

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

def typeProj [Finite Γ] {n : ℕ} (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) :
    Matrix (Fin n) (Fin n) K :=
  haveI : Fintype H := Fintype.ofFinite H
  ((Nat.card H : K)⁻¹) • ∑ h : H, (((χ h)⁻¹ : Kˣ) : K) • ρ (h : Γ)

end Proj

structure RepDat (K : Type) [Field K] [NumberField K] [StarRing K] (Γ : Type) [Group Γ] [Fintype Γ] (D0 D1 : ℕ) where

  Dg : ℕ

  Xg : InfinitePlace K → Matrix (Fin Dg) (Fin Dg) ℂ

  Rg : Submodule (𝓞 K) (Fin Dg → K)

  ρ : Γ →* Matrix (Fin Dg) (Fin Dg) K

  S : Type

  fS : Fintype S

  es : S → Matrix (Fin Dg) (Fin Dg) K

  nS : S → ℕ

  nbar : ℝ

  γ : ∀ s, Fin (nS s) → Γ

  ι0 : Matrix (Fin Dg) (Fin D0) K

  ι1 : Matrix (Fin Dg) (Fin D1) K

attribute [instance] RepDat.fS

namespace RepDat

end RepDat

end Formalism.L2.GlobalTheoryTheory.DivPassage2
