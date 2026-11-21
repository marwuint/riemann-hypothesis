import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Real

noncomputable section

def alternant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) : MvPolynomial ι ℚ :=
  (Matrix.of fun i i' : ι => (X i : MvPolynomial ι ℚ) ^ e i').det

def antisym {ι : Type*} [Fintype ι] [DecidableEq ι] (H : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  ∑ w : Equiv.Perm ι, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w H

def frobDim {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ((∑ a, la a).factorial : ℚ) *
      (∏ a : Fin r, ∏ b : Fin r,
        if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1) /
    ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ)

def FrobeniusRectangleBound.Statement : Prop :=
  ∀ (r s : ℕ) (ν : Fin r → ℕ), Antitone ν →
    frobDim (fun a => s + ν a) ≤
      ((r * s + ∑ a, ν a).choose (∑ a, ν a) : ℚ) * frobDim (fun _ : Fin r => s) * frobDim ν

abbrev RootPoly (f j k : ℕ) : Type := MvPolynomial (Fin f × (Fin j ⊕ Fin k)) ℝ

variable (f j k : ℕ)

def flagDim : ℕ := f * ((j + k) * (j + k - 1) / 2)

def vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) : R :=
  (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det

def fibre : RootPoly f j k :=
  ∏ τ : Fin f, if k ≤ j then
      vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Sum.inl a) : RootPoly f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Sum.inl a) : RootPoly f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k))

end

end GroundTheory.Heights₂.Heights
