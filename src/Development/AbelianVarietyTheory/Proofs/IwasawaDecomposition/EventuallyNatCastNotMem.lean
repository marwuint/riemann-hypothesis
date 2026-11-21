import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial

theorem eventually_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

end GlobalTheory.HeightCounting

end
