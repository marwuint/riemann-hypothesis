import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq

noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

def ShaOK (B : Pre) (s : ℕ → ℕ → ℚ) : Prop :=
  ∃ ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E (AlgebraicClosure B.host.E) p,
    ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → s p e = (n : ℚ)

abbrev Chi (B : Pre) : Type := ∀ k : Fin 2, Fin B.R.f → Fin B.R.m → (ZMod (B.host.g k))ˣ

structure IsSer (r g N : ℕ) (e : Polynomial (ZMod g) → MonoidAlgebra ℂ (GL (Fin r) (ZMod g))) : Prop where
  idem : ∀ f, e f * e f = e f
  central : ∀ f a, e f * a = a * e f
  orth : ∀ f f', f ≠ f' → e f * e f' = 0
  zero : ∀ f, e f = 0 ↔ ¬ (f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0)
  sum : ∃ S : Finset (Polynomial (ZMod g)),
    (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, e f = 1
  rat : ∀ f x, (e f).coeff x ∈
    IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))}

end GlobalTheory.MemN
