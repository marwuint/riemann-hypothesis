import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice

def join {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun p => Fin.lastCases (motive := fun _ => R) (ξ p.2) (fun i => u i p.2) p.1

def spec {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : MvPolynomial (Fin 1 × Fin N) E :=
  aeval (join (fun i j => C (s i j)) fun j => X (0, j)) f

def lin {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K := ∑ j, X ((0 : Fin 1), j) * C (y j)

def finPart {K ι : Type} [Field K] [NumberField K] (g : MvPolynomial ι K) : ℝ :=
  (∑ᶠ v : FinitePlace K, Real.log (gaussAbs v g)) / (Module.finrank ℚ K : ℝ)

def mean (K : Type) [Field K] [NumberField K] (a : (K →+* ℂ) → ℝ) : ℝ := (∑ τ, a τ) / (Module.finrank ℚ K : ℝ)

def NoSquare {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin 1 × Fin N) K) : Prop :=
  g ≠ 0 ∧ ∀ y : Fin N → K, y ≠ 0 → ¬ lin y ^ 2 ∣ g

theorem join_last {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (j : Fin N) : join u ξ (Fin.last D, j) = ξ j := by
  simp [join]

theorem join_castSucc {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (i : Fin D) (j : Fin N) :
    join u ξ (i.castSucc, j) = u i j := by
  simp [join]

namespace Check

theorem lin_ne {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : lin y ≠ 0 := by
  intro h
  apply hy
  funext j
  have := congrArg (eval (fun p : Fin 1 × Fin N => if p.2 = j then (1:K) else 0)) h
  simpa [lin] using this

end Check

end GlobalTheory.HSChoice
