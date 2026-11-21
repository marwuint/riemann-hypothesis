import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.WeilIntegral

set_option autoImplicit false in
open scoped TensorProduct in

theorem _root_.GlobalTheory.WeilIntegral.isAlgebraic_of_etale (S B : Type) [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.Etale S B] (f : B) : IsAlgebraic S f := by
  classical
  let K := FractionRing S
  haveI : Algebra.Etale K (TensorProduct S K B) := Algebra.Etale.baseChange S B K
  haveI : Module.Finite K (TensorProduct S K B) :=
    Algebra.FormallyUnramified.finite_of_free K (TensorProduct S K B)
  haveI hal : Algebra.IsAlgebraic K (TensorProduct S K B) := Algebra.IsAlgebraic.of_finite K _
  obtain ⟨p, hp0, hp⟩ := hal.isAlgebraic ((1 : K) ⊗ₜ[S] f)
  set q := IsLocalization.integerNormalization (nonZeroDivisors S) p
  have hq0 : q ≠ 0 := fun h0 =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h0)
  have hq : Polynomial.aeval ((1 : K) ⊗ₜ[S] f) q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ p hp
  have hmap : (1 : K) ⊗ₜ[S] Polynomial.aeval f q = 0 := by
    rw [← hq, ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply]
    rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).2 (TensorProduct.isBaseChange S B K)
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) (TensorProduct.mk S K B 1)).1 hmap
  refine ⟨Polynomial.C (s : S) * q, ?_, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.2 (nonZeroDivisors.coe_ne_zero s)) hq0
  · rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def]
    exact hs

end GlobalTheory.WeilIntegral
