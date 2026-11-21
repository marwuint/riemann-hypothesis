import Formalism.GaussJetBounds.StatementP

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def unitBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

def xMinors {K : Type} [Field K] {d N0 : ℕ} [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) :
    Set (MvPolynomial (ZMod d × Fin N0 × Fin N0) K) :=
  {P | ∃ A : ∀ s c, Fin (p s c) → Fin N0, P = ∏ s : ZMod d, minorProd
    (fun (i a : Fin N0) => (MvPolynomial.X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K))
    (p s) (hp s) (A s)}

def nablaO {K : Type} [NormedField K] [IsUltrametricDist K] {d N0 : ℕ} [NeZero d]
    (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) :
    Submodule (unitBall K) (MvPolynomial (ZMod d × Fin N0 × Fin N0) K) :=
  Submodule.span (unitBall K) (xMinors colN p hp)

end Formalism.DworkPowerSeriesWeights
