import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem tauE_injective' (D : D7) : Function.Injective (TH.tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((Formalism.BasicNotions.factEmb D.R D.host).1.1 h))

theorem tauE_surj' (D : D7) (φ : D.host.E →+* ℂ)
    (h : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) : ∃ ρ, TH.tauE D ρ = φ := by
  obtain ⟨g, rfl⟩ := (Formalism.BasicNotions.factEmb D.R D.host).1.2 φ
  exact ⟨D.eTau.symm ⟨g, ((Formalism.BasicNotions.factEmb D.R D.host).2 g).1 h⟩, by unfold TH.tauE; rw [Equiv.apply_symm_apply]⟩

theorem tauE_or' (D : D7) (φ : D.host.E →+* ℂ) :
    ∃ ρ, TH.tauE D ρ = φ ∨ TH.tauE D ρ = ComplexEmbedding.conjugate φ := by
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hs : D.host.sqrtMinusD * D.host.sqrtMinusD = -(D.host.d : D.host.E) := by
    apply D.host.φ₀.injective
    rw [map_mul, h0, map_neg, map_natCast, mul_mul_mul_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : φ D.host.sqrtMinusD * φ D.host.sqrtMinusD =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [← map_mul, hs, ← h0, ← map_mul, hs, map_neg, map_neg, map_natCast, map_natCast]
  rcases mul_self_eq_mul_self_iff.1 h1 with h | h
  · obtain ⟨ρ, e⟩ := tauE_surj' D φ h
    exact ⟨ρ, Or.inl e⟩
  · obtain ⟨ρ, e⟩ := tauE_surj' D (ComplexEmbedding.conjugate φ) (by
      rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring)
    exact ⟨ρ, Or.inr e⟩

end GlobalTheory.MassLink
