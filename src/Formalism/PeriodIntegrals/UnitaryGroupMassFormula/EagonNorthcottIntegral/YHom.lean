import Mathlib
import Formalism.PeriodIntegrals.EagonNorthcottZ

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

def sgn {D : ℕ} (i : Fin D) (J : Finset (Fin D)) : ℤ := (-1) ^ (J.filter (· < i)).card

abbrev P (D : ℕ) : Type := MvPolynomial (Fin D ⊕ Fin D) ℤ

abbrev S (D : ℕ) : Type := MvPolynomial (Fin D) ℤ

abbrev W (D : ℕ) : Type := Finset (Fin D) → P D

def K {D : ℕ} (t : Fin D → P D) (ω : W D) : W D :=
  fun J => ∑ i ∈ Jᶜ, (sgn i J : P D) * t i * ω (insert i J)

def ys {D : ℕ} : Fin D → P D := fun i => X (Sum.inr i)

def YHom {D : ℕ} (a : ℕ) (f : P D) : Prop := ∀ m ∈ f.support, ∑ i, m (Sum.inr i) = a

def Gr {D : ℕ} (a j : ℕ) (ω : W D) : Prop := (∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)

end PI.EagonNorthcottZ
