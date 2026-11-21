import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOne
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := _root_.GlobalTheory.HoweR.fock_lie_wts_comm P Q R S
  obtain ⟨hStab, hAdm⟩ := _root_.GlobalTheory.HoweR.coinv_stab_adm P Q R S x
  obtain ⟨α, β, hq⟩ := GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants P Q R S x
  obtain ⟨α', β', hqt⟩ := _root_.GlobalTheory.HoweR.QuadT.negT_fockAct2_quad P Q R S x
  refine ⟨⟨hLie, hWt, _root_.GlobalTheory.HoweR.fock_locU P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, _root_.GlobalTheory.HoweR.coinv_cycMod P Q R S x⟩

end GlobalTheory.HoweR
