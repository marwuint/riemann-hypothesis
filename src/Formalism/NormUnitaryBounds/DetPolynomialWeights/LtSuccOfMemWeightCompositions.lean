import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients

open MvPolynomial

noncomputable section

universe u

namespace Formalism.NormUnitaryCountingLemmas

namespace WeightCompositions

variable {N n : ℕ}

lemma sum_blockWt (d : (Fin N × Fin n) →₀ ℕ) :
    ∑ j, Finsupp.weight (blockWt N n) d j = ∑ p, d p := by
  simp only [Finsupp.weight_eq_sum, Finset.sum_apply, blockWt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply]

lemma weight_one (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (fun _ : Fin N × Fin n => (1 : ℕ)) d = ∑ p, d p := by
  simp [Finsupp.weight_eq_sum]

variable {K : Type u} [Field K] (ν : Fin N → ℕ)

lemma mem_block {F : MvPolynomial (Fin N × Fin n) K} (hF : F ∈ H K ν) :
    F ∈ weightedHomogeneousSubmodule K (blockWt N n) ν := by
  unfold H at hF
  exact (Submodule.mem_inf.mp hF).1

lemma H_le_total :
    H K (n := n) ν ≤
      weightedHomogeneousSubmodule K (fun _ : Fin N × Fin n => (1 : ℕ)) (∑ j, ν j) := by
  intro F hF
  have hb := mem_block ν hF
  rw [mem_weightedHomogeneousSubmodule] at hb ⊢
  intro d hd
  rw [weight_one, ← sum_blockWt, hb hd]

instance finiteDimensional_H : FiniteDimensional K (H K (n := n) ν) := by
  have : FiniteDimensional K
      (weightedHomogeneousSubmodule K (fun _ : Fin N × Fin n => (1 : ℕ)) (∑ j, ν j)) :=
    Module.Finite.iff_fg.mpr
      (weightedHomogeneousSubmodule_fg K _ (fun _ => one_ne_zero) _)
  exact Submodule.finiteDimensional_of_le (H_le_total ν)

end WeightCompositions

end Formalism.NormUnitaryCountingLemmas
