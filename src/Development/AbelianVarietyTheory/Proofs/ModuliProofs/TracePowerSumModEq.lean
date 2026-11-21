import Mathlib
open Polynomial

namespace GlobalTheory.TraceAeval

open Module

noncomputable def powMat {R : Type*} [CommRing R] (n : ℕ) (ψ : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((X ^ ((j : ℕ) + 1)) %ₘ ψ).coeff i

open Polynomial in
open Module in
theorem _root_.GlobalTheory.TraceAeval.powMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) {ψ : R[X]} (h : ψ.Monic) :
    (_root_.GlobalTheory.TraceAeval.powMat n ψ).map f = _root_.GlobalTheory.TraceAeval.powMat n (ψ.map f) := by
  ext i j
  simp only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow,
    Polynomial.map_X]

end GlobalTheory.TraceAeval
