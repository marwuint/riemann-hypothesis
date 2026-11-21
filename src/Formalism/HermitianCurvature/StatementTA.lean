import Mathlib
import Formalism.HermitianCurvature.StatementK

namespace Formalism.FourierDecayAlt.TA

open Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

abbrev Pt (E : Type) := List (ℕ × E)

def ext {E : Type} (h : Pt E) (s : ℕ) (t : E) : Pt E := h ++ [(s, t)]

def PSDOn {α : Type} (P : Finset α) (k : α → α → ℂ) : Prop :=
  (∀ x ∈ P, ∀ y ∈ P, k y x = conj (k x y)) ∧
  ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re

def LatSum {E : Type} [AddCommGroup E] (L : AddSubgroup E) (c : E → ℝ) (ep : ℝ) : Prop :=
  (∀ x, 0 ≤ c x) ∧ ∀ S : Finset E, (∀ x ∈ S, x ∈ L ∧ x ≠ 0) → ∑ x ∈ S, c x ≤ ep

structure Data (E : Type) [Field E] where
  r : ℕ
  K : ℕ → Pt E → Pt E → ℂ
  Th : ℕ → ℕ → E → Pt E → Pt E → ℂ
  e : ℕ → ℝ
  La : ℕ → ℕ → AddSubgroup E
  Lf : ℕ → ℕ → AddSubgroup E
  Lv : ℕ → AddSubgroup E

end Formalism.FourierDecayAlt.TA
