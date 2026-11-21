import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionEqSumKFiniteModule
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKFiniteModuleIrreducibleUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeSpaceHolomorphicKModuleKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingSpanEqSpanWords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSmoothVecOfIrreducibleUnitaryRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKType

open Matrix GlobalTheory.HolDS

namespace GlobalTheory.HolDS

theorem holomorphicDiscreteSeries_holds : GlobalTheory.Published.HolomorphicDiscreteSeries := by
  intro n ε lam hHC hHol H _ _ σ hDS
  obtain ⟨hc, hnt, hU, hI, -⟩ := id hDS
  haveI := hc
  haveI := hnt
  obtain ⟨D, E, hK⟩ := _root_.GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds n ε H σ hU hI
  have low := _root_.GlobalTheory.HolDS.lowKSub_kMod n ε H σ D E lam hHC hHol hDS hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun μ S hS => _root_.GlobalTheory.kType_weight_in_cone_over_lowK n ε H σ D E lam hHC hHol hDS hK μ S hS
  · exact fun v hv => _root_.GlobalTheory.HdSmooth.kFinite_smoothVec n ε H σ hU hI v hv
  · intro Z hZ v hv
    have hvD : v ∈ D := low.1 hv
    have hx : (⟨v, hvD⟩ : D) ∈ (Formalism.MainNotions.S.lowKSub ε lam σ).comap D.subtype := hv
    have h := _root_.GlobalTheory.HolomorphicDiscreteSeriesDecomposition.dRepC_eq_sum n ε H σ D E hK Z ⟨v, hvD⟩
    simp only at h
    rw [h]
    have h0 : (∑ a, ∑ b, Z a b • E a b ⟨v, hvD⟩ : D) = 0 := by
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : ε a = false ∧ ε b = true
      · rw [low.2.2.2 b a hab.2 hab.1 _ hx, smul_zero]
      · rw [hZ a b hab, zero_smul]
    rw [h0]
    rfl
  · intro v
    rw [_root_.GlobalTheory.HolDS.raisingSpan_eq_span_words n ε H σ D E hK _ low.1, _root_.GlobalTheory.kfin_span_raising_words_lowK n ε H σ D E lam hHC hHol hDS hK,
      Submodule.map_top, Submodule.range_subtype]
    exact (hK.mem v).symm

end GlobalTheory.HolDS
