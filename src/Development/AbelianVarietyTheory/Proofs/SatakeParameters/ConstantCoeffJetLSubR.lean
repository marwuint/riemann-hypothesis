import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KFormCore

section Generic

variable {K : Type} [Field K] {σ σ' δ δ' : Type}

def jetL (J : (δ →₀ ℕ) → K) : MvPolynomial (σ ⊕ δ) K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials (σ ⊕ δ) K).constr K fun m =>
    monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn))

theorem jetL_monomial (J : (δ →₀ ℕ) → K) (m : σ ⊕ δ →₀ ℕ) (c : K) :
    jetL J (monomial m c) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h1 : (monomial m c : MvPolynomial (σ ⊕ δ) K) = c • basisMonomials (σ ⊕ δ) K m := by
    simp [smul_monomial]
  rw [h1, map_smul, jetL, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

end Generic

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem applyAt0_eq (l : ℕ) [Fact l.Prime] (a b : ℕ) (Th : MvPowerSeries (ι × Fin a × Fin b) ℂ_[l])
    (Q : MvPolynomial (KM.XZ ι a b) ℤ) :
    KM.applyAt0 a b l Th Q = jetL (fun m => (m.prod fun _ k => (k.factorial : ℂ_[l])) * MvPowerSeries.coeff m Th)
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) := by
  conv_rhs => rw [Q.as_sum, map_sum, map_sum]
  unfold KM.applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_monomial, jetL_monomial, mul_assoc]
  rfl

end Main

end GlobalTheory.KFormCore
