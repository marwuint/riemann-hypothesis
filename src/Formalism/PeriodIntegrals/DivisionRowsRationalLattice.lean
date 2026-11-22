import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.LocalRingCardinality.DataArith

noncomputable section

namespace PI.Dv

open Formalism.BasicNotions

section Abstract

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

variable (A : HLat K) (ρ : Representation K G A.V)

def cutE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M ⊓ (LinearMap.range e).restrictScalars (𝓞 K)

def imgE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M.map (LinearMap.restrictScalars (𝓞 K) e)

def dimE (e : Module.End K A.V) : ℕ := Module.finrank K (LinearMap.range e)

def degL (M : Submodule (𝓞 K) A.V) : ℝ := (Formalism.HN.rkK M : ℝ) * Formalism.HN.muDef A.b A.X M

def muMaxL (M : Submodule (𝓞 K) A.V) : ℝ := Formalism.HN.muMaxDef A.b A.X M

def lenAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℕ∞ :=
  letI : w.asIdeal.IsPrime := w.isPrime
  Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (↥M ⧸ N.comap M.subtype))

def idxAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℤ :=
  ((lenAt w M N).toNat : ℤ) - ((lenAt w N M).toNat : ℤ)

def LocLe {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) (F : ℕ)
    (M N : Submodule (𝓞 K) V) : Prop :=
  ∀ x ∈ M, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ (w.asIdeal ^ F) • N

def IsFull (M : Submodule (𝓞 K) A.V) : Prop := M.FG ∧ Submodule.span K (M : Set A.V) = ⊤

def IsProj (e : Module.End K A.V) (n : ℕ) : Prop :=
  A.Good ∧ 0 < n ∧ e * e = e ∧ (∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • e x ∈ A.L) ∧
  ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) y = Formalism.HermitianLatticesTheory.majAt A.b A.X v x (e y)

end Abstract

section Lemma2

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def ProjectionSandwichLength (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  (∀ x ∈ imgE A e A.L, ((n : ℕ) : 𝓞 K) • x ∈ cutE A e A.L) ∧
  cutE A e A.L ≤ imgE A e A.L ∧
  Nonempty ((↥(imgE A e A.L) ⧸ (cutE A e A.L).comap (imgE A e A.L).subtype) ≃ₗ[𝓞 K]
    (↥(imgE A (1 - e) A.L) ⧸ (cutE A (1 - e) A.L).comap (imgE A (1 - e) A.L).subtype)) ∧
  (∀ w : HeightOneSpectrum (𝓞 K),
    idxAt w (imgE A e A.L) (cutE A e A.L) = idxAt w (imgE A (1 - e) A.L) (cutE A (1 - e) A.L) ∧
    0 ≤ idxAt w (imgE A e A.L) (cutE A e A.L) ∧
    idxAt w (imgE A e A.L) (cutE A e A.L) ≤
      (min (dimE A e) (dimE A (1 - e)) : ℕ) * vAdd w ((n : ℕ) : K)) ∧
  (∀ ψ : Module.Dual K A.V, ψ ∘ₗ e = ψ →
    (ψ ∈ Formalism.HN.dualLat (cutE A e A.L) ↔ ∃ φ ∈ A.dualL, ψ = φ ∘ₗ e))

def DegreeKernelLowerBound (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  degL A A.L - (dimE A (1 - e) : ℝ) * (muMaxL A A.L + 2 * Real.log (n : ℝ)) ≤ degL A (cutE A e A.L)

def KernelIndexFullLattice (A : HLat K) (e : Module.End K A.V) : Prop :=
  ∀ Th : Submodule (𝓞 K) A.V, IsFull A Th →
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w F Th A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th - (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w 0 ((w.asIdeal ^ F) • Th) A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th + (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    cutE A e Th ≤ imgE A e Th

def projection_lemma_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ), IsProj A e n → ProjectionSandwichLength A e n ∧ DegreeKernelLowerBound A e n ∧ KernelIndexFullLattice A e

end Lemma2

section Herm

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

def IsCM (z : K) : Prop := ∀ σ : K →+* ℂ, σ (star z) = star (σ z)

def IsConjPlK (w w' : HeightOneSpectrum (𝓞 K)) : Prop := ∀ x : K, vAdd w' x = vAdd w (star x)

def IsHermE (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ x y, h y x = star (h x y)) ∧ (∀ x, (∀ y, h x y = 0) → x = 0) ∧ ∀ x y, h (e x) y = h x (e y)

def IsBasisAt (A : HLat K) {d : ℕ} (a : Fin d → A.V) (M : Submodule (𝓞 K) A.V)
    (w w' : HeightOneSpectrum (𝓞 K)) : Prop :=
  LinearIndependent K a ∧ ∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
    LocLe u 0 (Submodule.span (𝓞 K) (Set.range a)) M ∧ LocLe u 0 M (Submodule.span (𝓞 K) (Set.range a))

def LamStar (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (y : A.V) : Prop :=
  y ∈ LinearMap.range e ∧ (∀ u ∈ U, h y u = 0) ∧
  ∀ m ∈ cutE A e A.L, h y m ∈ Set.range (algebraMap (𝓞 K) K)

def IsValG (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Prop :=
  ∃ w', IsConjPlK w w' ∧ ∃ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y ∧
    (∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
      (∀ i, ∃ s : 𝓞 K, s ∉ u.asIdeal ∧ LamStar A e h U (s • y i)) ∧
      ∀ z, LamStar A e h U z → ∃ s : 𝓞 K, s ∉ u.asIdeal ∧
        s • z ∈ Submodule.span (𝓞 K) (Set.range y)) ∧
    n = - vAdd w (Matrix.of fun i j => h (y i) (y j)).det

def L7 (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    (∀ w k, IsValG A e h U w k →
      k ≤ ((dimE A e : ℤ) - (Module.finrank K U : ℤ)) * vAdd w ((n : ℕ) : K)) ∧
    (∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) ≤
        ∑ᶠ w, lw K w * (γ w : ℝ)) ∧
    (∀ φ ∈ A.dualL, (∀ u ∈ U, φ u = 0) →
      ∀ m ∈ cutE A e A.L, φ m ∈ Set.range (algebraMap (𝓞 K) K))

end Herm

end PI.Dv
