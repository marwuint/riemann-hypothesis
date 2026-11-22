import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocus

open GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal → algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := GlobalTheory.LocDivEtale.exists_dvd_mul_pow
