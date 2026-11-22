import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrFormNZ

theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ C : Matrix (Fin r) κ F, ∀ j, C *ᵥ a j = Pi.single j 1 := by
  have hinj : Function.Injective (Fintype.linearCombination F a) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' L, fun j => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have := LinearMap.congr_fun hL (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using this

end GlobalTheory.LagrFormNZ

namespace GlobalTheory.LagrFormNZ

end GlobalTheory.LagrFormNZ
