import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.RecMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.JumpsAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem infOf_of_weights {n : ℕ} (m : Fin n → ℤ) (μ : Multiset ℂ)
    (h : (Finset.univ.val.map fun i => -m i).map (fun n : ℤ => (n : ℂ)) = μ.map fun z => ((n : ℂ) - 1) / 2 - z) :
    μ = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id', Int.cast_neg, sub_neg_eq_add] at h2
  exact h2.symm

private theorem exists_over (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hl : (l : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ¬ IsUnit (l : 𝓞 F) := fun hu => by
    have h := hu.map (Algebra.norm ℤ)
    rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne'] at h
    exact (Nat.prime_iff_prime_int.1 Fact.out).not_unit h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(l : 𝓞 F)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (l : 𝓞 F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨P, hP.isPrime, fun h0 => hl (by rw [h0] at hmem; exact hmem)⟩, hmem⟩

end UpperTheory.V.Af
