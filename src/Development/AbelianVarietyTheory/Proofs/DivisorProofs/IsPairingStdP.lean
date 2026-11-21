import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

section Real

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

def schrF (P : V → V → ℝ) (w : V × V) (f : V → ℂ) : V → ℂ :=
  fun y => Complex.exp (-(2 * Real.pi * Complex.I) * ((P y w.2 + P w.1 w.2 / 2 : ℝ) : ℂ)) * f (y + w.1)

def omega (P : V → V → ℝ) (w w' : V × V) : ℝ := P w.1 w'.2 - P w'.1 w.2

structure IsPairing (P : V → V → ℝ) : Prop where
  addL : ∀ x x' y, P (x + x') y = P x y + P x' y
  addR : ∀ x y y', P x (y + y') = P x y + P x y'
  smulL : ∀ (c : ℝ) x y, P (c • x) y = c * P x y
  smulR : ∀ (c : ℝ) x y, P x (c • y) = c * P x y
  nondegL : ∀ x, (∀ y, P x y = 0) → x = 0
  nondegR : ∀ y, (∀ x, P x y = 0) → y = 0

structure Setup (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V)) : Prop where
  pair : IsPairing P
  pair₁ : IsPairing P₁
  add : ∀ w w', j (w + w') = j w + j w'
  smul : ∀ (c : ℝ) w, j (c • w) = c • j w
  symp : ∀ w w', omega P (j w) (j w') = omega P₁ w w'
  iso : ∀ l ∈ L, ∀ l' ∈ L, omega P l l' = 0
  orth : ∀ l ∈ L, ∀ w, omega P l (j w) = 0
  max : ∀ v, (∀ l ∈ L, omega P v l = 0) → (∀ w, omega P v (j w) = 0) → v ∈ L

theorem IsPairing.zero_left {P : V → V → ℝ} (h : IsPairing P) (y : V) : P 0 y = 0 := by
  simpa using h.smulL 0 0 y

theorem IsPairing.zero_right {P : V → V → ℝ} (h : IsPairing P) (x : V) : P x 0 = 0 := by
  simpa using h.smulR 0 x 0

end Real

section Adelic

open scoped Matrix
open NumberField GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def trP (κ : Type) [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i)

def locV {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

end Adelic

end GlobalTheory.ArchUniq
