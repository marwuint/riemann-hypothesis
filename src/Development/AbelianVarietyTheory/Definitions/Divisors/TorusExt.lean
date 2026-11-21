import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LieHt

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

def MuLe (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (ν : ℝ) : Prop :=
  ∀ W ≤ L, deg h W ≤ latRank K W * ν

def Full (L : Submodule (𝓞 K) (Fin m → K)) : Prop := L.FG ∧ Submodule.span K (L : Set (Fin m → K)) = ⊤

def lineLat (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) : Submodule (𝓞 K) (Fin m → K) :=
  L ⊓ (Submodule.span K {x}).restrictScalars (𝓞 K)

variable (K' : Type) [Field K'] [NumberField K'] [Algebra K K']

def latBC (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K') (Fin m → K') :=
  Submodule.span (𝓞 K') ((fun v i => algebraMap K K' (v i)) '' (L : Set (Fin m → K)))

variable {K'} in

def IsBC (h : HermFam K (Fin m → K)) (h' : HermFam K' (Fin m → K')) : Prop :=
  ∀ (σ : K' →+* ℂ) (i j : Fin m),
    h'.form σ (Pi.single i 1) (Pi.single j 1) = h.form (σ.comp (algebraMap K K')) (Pi.single i 1) (Pi.single j 1)

end Lat

structure SemiFib (K : Type) [Field K] [NumberField K] : Type 1 where

  P₀ : Out.PolAV (Sp K)

  G : Over (Sp (𝓞 K))
  [grp : GrpObj G]
  semi : IsSemiAbelian G

  φ : P₀.A.left ⟶ G.left
  fib : IsGrpPullback P₀.A G (spMap (algebraMap (𝓞 K) K)) φ

  v : Fin P₀.g → (epsR K ⟶ P₀.A)
  basis : IsLieBasis v

attribute [instance] SemiFib.grp

namespace SemiFib

variable {K : Type} [Field K] [NumberField K] (F : SemiFib K)

def lieLat : Submodule (𝓞 K) (Fin F.P₀.g → K) := Submodule.span (𝓞 K)
  {c | ∃ u : epsR (𝓞 K) ⟶ F.G, IsTangent u ∧ ∃ w, IsVecOver (algebraMap (𝓞 K) K) F.φ u w ∧ IsLieComb c F.v w}

def IsUnif (s : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (W : Fin F.P₀.g → Fin g → ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (e : Q.g = g) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
    (u : HolUnif Q.A Q.L g) (χ : u.Λ → ℂ),
    IsPolFibre s F.P₀ Q ψ ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ ∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)

def IsHerm (h : HermFam K (Fin F.P₀.g → K)) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
    (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
      ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)

def IsRho (ρ : (K →+* ℂ) → ℝ) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
    (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
      IsLeast {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} (ρ s)

def falt (h : HermFam K (Fin F.P₀.g → K)) : ℝ := -deg h F.lieLat

end SemiFib

end GlobalTheory.LieHt
end
