import Formalism.DegreeFormula.FlagDegFormula

open MvPolynomial

namespace Formalism.DegreeFormula.PermutationPointDegree
open Formalism.DegreeFormula

theorem permExp_inj {ι : Type} [Fintype ι] {N : ℕ} (σ ρ : ι → Equiv.Perm (Fin N))
    (h : permExp σ = permExp ρ) : σ = ρ := by
  funext τ
  ext i
  have := DFunLike.congr_fun h (τ, i)
  simp only [permExp, Finsupp.equivFunOnFinite_symm_apply_apply] at this
  have h1 := (σ τ i).isLt
  have h2 := (ρ τ i).isLt
  omega

theorem sum_delta (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [← Finset.sum_range_id]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv Fin.revPerm _ _ ?_
  intro i
  simp [Fin.val_rev]
  omega

end Formalism.DegreeFormula.PermutationPointDegree

namespace Formalism.DegreeFormula

end Formalism.DegreeFormula
