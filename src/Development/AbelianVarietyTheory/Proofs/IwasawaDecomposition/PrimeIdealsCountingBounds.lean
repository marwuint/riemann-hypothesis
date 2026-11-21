import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeMemHeightOneSpectrum

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.FewPrimes

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | (apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target ..)

end GlobalTheory.Mem.FewPrimes
