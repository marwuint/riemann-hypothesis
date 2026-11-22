import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairsExistAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatMulVecSec
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.HostConjugateIdeal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLastValuationNeOfRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrMemOfMemLatV

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeData

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_fin_int (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem splitPlace_valuation_cmImaginaryGenerator_eq_one (p : SplitPt D k) (hp : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  obtain ⟨h1, h2⟩ := hp.1 _ (e_mem_intAt p)
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h3 := pr_mem_of_fin_int p h1.2
  have h4 := pr_mem_of_fin_int p h2.2
  rw [RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff] at h3 h4
  have h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
      RingHom.map_one, map_one]
  refine le_antisymm h3 ?_
  rw [← h5]
  exact mul_le_of_le_one_right' h4

theorem splitPlace_valuation_neg_cmGenerator_pow_eq_one (p : SplitPt D k) (hp : p.UnitAA) (n : ℕ) :
    valuation k (p.pr (incA D (-D.host.xi0 ^ n))) = 1 ∧ valuation k (p.pr (incA D (star (-D.host.xi0 ^ n)))) = 1 := by
  have h := splitPlace_valuation_cmImaginaryGenerator_eq_one p hp
  refine ⟨?_, ?_⟩
  · rw [RingHom.map_neg, RingHom.map_neg, RingHom.map_pow, RingHom.map_pow, Valuation.map_neg, map_pow, h, one_pow]
  · rw [star_neg, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, RingHom.map_neg, RingHom.map_pow, RingHom.map_pow,
      RingHom.map_neg, RingHom.map_neg, Valuation.map_neg, map_pow, Valuation.map_neg, h, one_pow]

end GlobalTheory.LevPrimeData

