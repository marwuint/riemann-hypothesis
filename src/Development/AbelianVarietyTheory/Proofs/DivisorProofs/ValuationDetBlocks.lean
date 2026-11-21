import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerFactorEqOneOfExpAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeConjugateSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open GlobalTheory.SplitFlip (omA omB invT IsUnif mem_KO_iff isOpen_KO)
open GlobalTheory.StdLocZeta (StdSupp stdDatum)
open GlobalTheory.StdLoc (glVol blockIdx)
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.LocStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Level

variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem mem_image_KO {M : Matrix D D k} :
    M ∈ Units.val '' (KO k D : Set (GL D k)) ↔ (∀ i j, M i j ∈ 𝒪[k]) ∧ valuation k M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨((mem_KO_iff g).1 hg).1, SplitFlip.valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let N : Matrix D D 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
    have hu : IsUnit N.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu', e]

theorem mem_KO_iff_det {g : GL D k} : g ∈ KO k D ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ valuation k g.val.det = 1 := by
  rw [← mem_image_KO]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨u, hu, e⟩ => Units.ext e ▸ hu⟩

variable {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D)

variable [MeasurableSpace k] [BorelSpace k]

end Level

end GlobalTheory.LocStd

end
