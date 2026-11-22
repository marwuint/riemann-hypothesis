import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section
open GroundTheory.Global

namespace GlobalTheory.SubstIntertw

variable (F : Type) [Field F] [NumberField F]

def stdChar : AddChar (AF F) ℂ where
  toFun a := (adelicChar F a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem stdChar_inl (z : InfiniteAdeleRing F) :
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (infiniteAdeleInl z : AF F)) : ℝ)) =
      (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [h2, GlobalTheory.AdelicSvN.Weyl.trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_stdChar : IsStd (stdChar F) := by
  refine ⟨continuous_subtype_val.comp continuous_adelicChar, fun x => ?_, fun a ha => ?_⟩
  · show (adelicChar F (algebraMap F (AF F) x) : ℂ) = 1
    rw [adelicChar_algebraMap]; rfl
  · have h0 : evI F ((0, 1) : AF F) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    have h2 : a.2 = 0 := by
      have := congrArg Prod.snd (ha ((0, 1) : AF F) h0)
      have e : (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 := this
      simpa using e
    obtain ⟨z, rfl⟩ : ∃ z : InfiniteAdeleRing F, a = infiniteAdeleInl z := ⟨a.1, Prod.ext rfl h2⟩
    exact (stdChar_inl F z).symm

end GlobalTheory.SubstIntertw

namespace GlobalTheory.SubstIntertw

end GlobalTheory.SubstIntertw
