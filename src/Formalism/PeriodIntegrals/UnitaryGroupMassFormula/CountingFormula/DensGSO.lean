module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

theorem isIntegral_iff_mem_integer (F : Type) [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · exact fun h => (Valuation.integer.integers _).mem_of_integral h
  · intro h
    have e : a = algebraMap 𝒪[F] F ⟨a, h⟩ := rfl
    rw [e]
    exact isIntegral_algebraMap

theorem integral_split_count : OSplit := by
  intro F E _ _ _ _ _ _ L _ e x
  rw [L.O_def]
  have key : IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[F] (e x) := by
    constructor
    · exact fun h => h.map ((e : E →ₐ[F] F × F).restrictScalars 𝒪[F])
    · intro h
      simpa using h.map ((e.symm : F × F →ₐ[F] E).restrictScalars 𝒪[F])
  rw [key]
  constructor
  · intro h
    exact ⟨(isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.fst 𝒪[F] F F)),
      (isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.snd 𝒪[F] F F))⟩
  · rintro ⟨h1, h2⟩
    exact IsIntegral.pair ((isIntegral_iff_mem_integer F _).2 h1) ((isIntegral_iff_mem_integer F _).2 h2)

end PI.UnitaryGroupMassFormula.CntFormula
