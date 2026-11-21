import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich.Model

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem xi_eq (ε : PreTilt O p) : xi ε = ReciprocityTheory.PGsh.Ainf.xi p O ε := rfl

theorem nu_eq (ε : PreTilt O p) : nu ε = ReciprocityTheory.PGsh.Ainf.nu p O ε := rfl

section Field

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

theorem theta_mu : fontaineTheta O p (mu ε) = 0 := by
  rw [← xi_mul_nu, map_mul, xi_eq, ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε, zero_mul]

theorem mu_ne_zero : mu ε ≠ 0 := by
  intro h
  rw [← xi_mul_nu, mul_comm] at h
  have := ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ h
  exact ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε (by rw [← nu_eq, this, map_zero])

omit hε [IsAlgClosed C] in
theorem isDomain_Ainf : IsDomain (Ainf p O) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

end Field

end GlobalTheory.Sandwich.Model
