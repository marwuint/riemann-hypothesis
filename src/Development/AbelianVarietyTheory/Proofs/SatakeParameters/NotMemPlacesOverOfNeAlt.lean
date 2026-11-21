import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterMonodromyZeroOfUnramified
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolLpCharOfUnr

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.InertialTypes

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E p) : w ∉ placesOver E q := by
  intro hw'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b hw')

end GlobalTheory.InertialTypes
