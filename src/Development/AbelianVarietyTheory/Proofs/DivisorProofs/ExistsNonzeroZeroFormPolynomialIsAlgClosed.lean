import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

open IsLocalRing

namespace GlobalTheory
namespace TsenCount

open Polynomial

variable {σ k : Type} [CommRing k]

def CoeffHom (e : ℕ) (p : (MvPolynomial σ k)[X]) : Prop := ∀ j, (p.coeff j).IsHomogeneous e

theorem CoeffHom.mul {a b : ℕ} {p q : (MvPolynomial σ k)[X]} (hp : CoeffHom a p)
    (hq : CoeffHom b q) : CoeffHom (a + b) (p * q) := fun j => by
  rw [coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ => (hp _).mul (hq _)

theorem coeffHom_map (g : k[X]) :
    CoeffHom 0 (g.map (MvPolynomial.C : k →+* MvPolynomial σ k)) := fun j => by
  rw [coeff_map]
  exact MvPolynomial.isHomogeneous_C _ _

theorem coeffHom_one : CoeffHom 0 (1 : (MvPolynomial σ k)[X]) := by
  simpa using coeffHom_map (σ := σ) (1 : k[X])

theorem CoeffHom.pow {p : (MvPolynomial σ k)[X]} (hp : CoeffHom 1 p) (m : ℕ) :
    CoeffHom m (p ^ m) := by
  induction m with
  | zero => simpa using coeffHom_one
  | succ m ih => rw [pow_succ]; exact ih.mul hp

theorem CoeffHom.sum {ι : Type} (s : Finset ι) (e : ℕ) (p : ι → (MvPolynomial σ k)[X])
    (h : ∀ i ∈ s, CoeffHom e (p i)) : CoeffHom e (∑ i ∈ s, p i) := fun j => by
  rw [finsetSum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => h i hi j

end TsenCount

end GlobalTheory
