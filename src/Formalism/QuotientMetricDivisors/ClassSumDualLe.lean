import Mathlib
import Formalism.QuotientMetricDivisors.Statement

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cutLat {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  A.comap ((Matrix.mulVecLin E).restrictScalars (𝓞 K))

def IsOrthProj {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) : Prop :=
  Pr * E = 1 ∧ Eᴴ * H * (1 - E * Pr) = 0

def IsClassSum {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    (H : Matrix (Fin n) (Fin n) K) (I : (Fin n → K) →ₗ[K] (Cl → V))
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (g : Cl → ℕ) : Prop :=
  ∀ x y, hform H x y = ∑ c, ((g c : K))⁻¹ * pair (I x c) (I y c)

end Defs

def OrthProjExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      Hᴴ = H ∧ IsUnit H.det ∧ IsUnit (Eᴴ * H * E).det ∧
        IsOrthProj H E ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)) ∧
        ∀ Pr, IsOrthProj H E Pr → Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H)

def ProjDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A) = cutLat E (Formalism.HermitianLatticesTheory.dual (hform H) A)

def CutDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (cutLat E A) = matLat Pr (Formalism.HermitianLatticesTheory.dual (hform H) A)

def ExpIndexLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (A B : Submodule (𝓞 K) (Fin D → K)), Submodule.IsLattice K A → Submodule.IsLattice K B →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ x ∈ A, a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) →
      idx w A B ≤ (D : ℤ) * vw w (a : K)

def ProjIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G0 : Type) [Fintype G0]
    (r : G0 → Matrix (Fin n) (Fin n) K) (c : G0 → K) (G : ℕ),
    (∀ s, ∃ a : 𝓞 K, (a : K) = (G : K) * c s) →
    ∀ B : Submodule (𝓞 K) (Fin n → K), (∀ s, ∀ x ∈ B, (r s).mulVec x ∈ B) →
    ∀ x ∈ B, (G : 𝓞 K) • (∑ s, c s • r s).mulVec x ∈ B

def BoundsI : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A →
    ∀ s : ℕ, (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ G : ℕ, (∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A) →
      Submodule.IsLattice K (cutLat E A) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E A), ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E A

def BoundsIVGen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ z ∈ cutLat E A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsLattice K (matLat Pr A) ∧ Submodule.IsLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * (vw w (a : K) + vw w (DG : K))

def BoundsIV : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E A, (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsLattice K (matLat Pr A) ∧ Submodule.IsLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K))

end Formalism.DivisionValues
