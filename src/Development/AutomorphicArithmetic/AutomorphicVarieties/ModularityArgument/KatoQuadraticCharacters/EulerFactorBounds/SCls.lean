module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

theorem sCls : SCls := by
  intro Ω _ _ _ ε X l _ n
  obtain ⟨hsurj, hinj, hmul, hone, hsmul, hmap, hsucc⟩ := H3.cls_props Ω ε X l n
  have hdiv : ∀ f f' : X.Kˣ, X.cls l n (f / f') = X.cls l n f - X.cls l n f' := by
    intro f f'
    have h := hmul (f / f') f'
    rw [div_mul_cancel] at h
    rw [h]
    abel
  have hpow : ∀ (f : X.Kˣ) (k : ℕ), X.cls l n (f ^ k) = k • X.cls l n f := by
    intro f k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, hmul, ih, succ_nsmul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hf : (f : X.K) ≠ 0 := f.ne_zero
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (clsK X l n (f : X.K)) = X.cls l n f
    unfold clsK
    rw [dite_eq_left hf, Units.mk0_val]
    unfold liftK
    exact Classical.epsilon_spec (p := fun b => (AdicCompletion.eval (idl l) (X.Kl l) n) b = X.cls l n f)
      (AdicCompletion.eval_surjective (idl l) (X.Kl l) n (X.cls l n f))
  · intro f f' a a' ha ha'
    refine ⟨?_, ?_⟩
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a + a') = X.cls l n (f * f')
      rw [map_add (f := _), hmul, ha, ha']
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a - a') = X.cls l n (f / f')
      rw [map_sub, hdiv, ha, ha']
  · intro f a k ha
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ k)
    rw [map_nsmul, hpow, ha]
  · intro f f' a a' ha ha' hc
    obtain ⟨g, hg⟩ := hc
    rw [map_sub, ha, ha', (hinj f f').2 ⟨g, hg⟩, sub_self]
  · intro φ f a ha
    exact hmap φ a f ha
  · exact fun f a ha => hsucc a f ha
  · intro f k a ha
    refine ⟨((PadicInt.toZModPow n) k).val, ?_⟩
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ ((PadicInt.toZModPow n) k).val)
    rw [map_smul, ha, hsmul]

end UpperTheory.V.Z.Kato.Nb

end
