import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TupleCharAtType

theorem natCast_notMem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 E) ∉ v.asIdeal := fun hv' => by
  obtain ⟨s, t, hst⟩ : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnitAt_of_notMem {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} (u : 𝓞 E)
    (hu : (u : E) ≠ 0) (hv : u ∉ v.asIdeal) : IsUnitAt v (atFin v (Units.mk0 (u : E) hu)) := by
  show Valued.v ((u : E) : v.adicCompletion E) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv

end GlobalTheory.TupleCharAtType
