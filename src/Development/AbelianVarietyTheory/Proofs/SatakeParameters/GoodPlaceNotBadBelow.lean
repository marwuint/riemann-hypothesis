import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodOffBad

theorem conj_eq_complexConj (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem isConjPl_conjPlE_left {D : D7} (P : PlE D.host) : IsConjPl D.host (GlobalTheory.SplitConjPlace.conjPlE P) P := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E x = y := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, conj_eq_complexConj]
  rw [this]

theorem conjPlE_mem_placesOver {D : D7} (P : PlE D.host) (p : ℕ) :
    GlobalTheory.SplitConjPlace.conjPlE P ∈ placesOver D.host.E p ↔ P ∈ placesOver D.host.E p := by
  show ((p : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.SplitConjPlace.conjPlE P).asIdeal ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]

end GlobalTheory.GoodOffBad
