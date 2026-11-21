import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.UnramCompletion

variable {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))

theorem intValuation_eq_of_notMem_sq {a : 𝓞 E} (h1 : a ∈ Q.asIdeal) (h2 : a ∉ Q.asIdeal ^ 2) :
    Q.intValuation a = exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have e1 := (Q.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)
  have e2 := mt (Q.intValuation_le_pow_iff_mem a 2).1 h2
  have h0 : Q.intValuation a ≠ 0 := Q.intValuation_ne_zero a ha
  rw [← exp_log h0] at e1 e2 ⊢
  rw [exp_le_exp] at e1 e2
  congr 1
  push_cast at e1 e2
  omega

theorem ringHom_ext_of_continuous {f g : Q.adicCompletion E → Q.adicCompletion E}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ k : E, f (algebraMap E _ k) = g (algebraMap E _ k)) : f = g :=
  (denseRange_algebraMap E Q).equalizer hf hg (funext h)

theorem exists_ringEquiv (c : E ≃+* E) (hc : Mem.Chr.ConjPl c Q Q) :
    ∃ σ : Q.adicCompletion E ≃+* Q.adicCompletion E, Continuous σ ∧
      (∀ k : E, σ (algebraMap E _ k) = algebraMap E _ (c k)) ∧ ∀ x, Valued.v (σ x) = Valued.v x := by
  obtain ⟨s, s1, s2, s3⟩ := Mem.Chr.exists_finCompl_map c hc
  obtain ⟨t, t1, t2, -⟩ := Mem.Chr.exists_finCompl_map c.symm ((Mem.Chr.conjPl_symm_iff c Q Q).2 hc)
  refine ⟨RingEquiv.ofRingHom s t ?_ ?_, s1, s2, s3⟩
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (s1.comp t1) continuous_id fun k => by
      simp [s2, t2])
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (t1.comp s1) continuous_id fun k => by
      simp [s2, t2])

theorem intAt_iff (x : E) : Formalism.L2.Col.IntAt Q x ↔ Q.valuation E x ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 := congrArg (Q.valuation E) h
    rw [map_mul, (valuation_eq_one_iff_notMem Q).2 hs, one_mul] at h1
    rw [h1]
    exact Q.valuation_le_one r
  · intro hx
    obtain ⟨n, d, h⟩ := Q.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

end GlobalTheory.UnramCompletion

open Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory.UnramCompletion

end GlobalTheory.UnramCompletion
