import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding

noncomputable section

open MeasureTheory Matrix Topology Set Filter GlobalTheory.Doubling GlobalTheory.EisCont
open CompanionTheory.D.gk.admitted.Gard (contDiff_integral_comp contDiff_Phi isCompact_mul_inv integral_mul_right_of_conj)
open scoped ContDiff NNReal

namespace GlobalTheory.EisCont.Smooth

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem isOpenEmbedding_val (N : ℕ) : IsOpenEmbedding (Units.val : GL (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
  haveI : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℝ _
  Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  (j : H →* G) (ι : H →* Matrix (Fin N) (Fin N) ℂ)

variable {j ι} {φ : G → ℂ}

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

theorem isCompact_preimage (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {T : Set (Matrix (Fin N) (Fin N) ℂ)}
    (hT : IsCompact T) : IsCompact (ι ⁻¹' T) := by
  have h2 : IsCompact (Units.val ⁻¹' (T ∩ {B | ‖B.det‖ = 1})) := (isOpenEmbedding_val N).isInducing.isCompact_preimage'
    (hT.inter_right (isClosed_eq continuous_id.matrix_det.norm continuous_const)) fun B hB =>
      (Matrix.isUnit_iff_isUnit_det B).2 (IsUnit.mk0 _ fun e => by simpa [e] using hB.2)
  convert (GlobalTheory.SmoothFactor.isClosedEmbedding_toHomUnits (ι := ι) hι).isCompact_preimage h2 using 1
  exact Set.ext fun y => (and_iff_left (h1 y)).symm

structure IsBump (f : Matrix (Fin N) (Fin N) ℂ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  nonneg : 0 ≤ f
  one : f 1 ≠ 0
  supp : ∃ S, IsCompact S ∧ (∀ B ∈ S, B.det ≠ 0) ∧ ∀ y, f y ≠ 0 → y ∈ S
  conj : ∀ k ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ y, f (kᴴ * y * k) = f y

variable {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

variable (hj : Continuous j) {ψ : G → ℂ}
include hj

end Abstract

end GlobalTheory.EisCont.Smooth

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel
  GlobalTheory.RegSW GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
