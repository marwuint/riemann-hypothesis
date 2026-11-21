import Mathlib

noncomputable section

open Classical

namespace Formalism.WachCohomologyFacts.Top

def sg (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i - ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def InWin (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 0 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ h

def Low (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (InWin G h η)

def Cl (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U - Low G h η U

def GlobalTheory (w t : ℕ) : Finset ℤ := Finset.Icc (w : ℤ) ((w : ℤ) + t - 1)

def T1 (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ

def T2 (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ Low G h η U, ∀ y ∈ GlobalTheory w t, σ + 2 < |x - y|

end Formalism.WachCohomologyFacts.Top
