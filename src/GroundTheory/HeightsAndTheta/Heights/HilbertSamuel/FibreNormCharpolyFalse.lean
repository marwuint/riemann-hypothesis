import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormCharpoly

theorem aeval_mul_of_isHomogeneous {σ' Ω : Type*} [Field Ω] [CharZero Ω] {p : MvPolynomial σ' ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (μ : Ω) (f : σ' → Ω) :
    aeval (fun j => μ * f j) p = μ ^ d * aeval f p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end FibreNormCharpoly

namespace ProjLine

open ProjLine

def Lc : Fin 2 → MRing (GlobalTheory (Fin 2)) :=
  ![X ⟨(), 0⟩ * X ⟨(), 1⟩, X ⟨(), 0⟩ ^ 2 + X ⟨(), 1⟩ ^ 2]

theorem Lc_zero : Lc 0 = X ⟨(), 0⟩ * X ⟨(), 1⟩ := rfl

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
