import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace CIndEncPf

theorem colSum_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (τ : E →+* ℂ) (hτ : InPsi H τ) (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))) :
    ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
      (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
  have h0 := hP.1.1
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h0
  have h1 := h0 τ hτ i i'
  rw [← h1]
  simp only [lap, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [LinearMap.sum_apply]
  rfl

end CIndEncPf

end Formalism.MainNotions.ModuliIntegralCharts.H1
