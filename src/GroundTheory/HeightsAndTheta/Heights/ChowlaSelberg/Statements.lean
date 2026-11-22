import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian Filter Topology
open scoped nonZeroDivisors Real ModularForm UpperHalfPlane

noncomputable section

def scaleLattice (c : ℂ) (Λ : Submodule ℤ ℂ) : Submodule ℤ ℂ := Λ.map (LinearMap.mulLeft ℤ c)

variable {K : Type} [Field K] [NumberField K]

def IsPeriodLattice (W : WeierstrassCurve ℂ) (Λ : Submodule ℤ ℂ) : Prop :=
  ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ),
    C • weierstrassCurve L = W ∧ Λ = scaleLattice (C.u : ℂ) L.lattice

structure CMFamily (K : Type) [Field K] [NumberField K] where

  k : Type
  [field : Field k]
  [numberField : NumberField k]
  [algebra : Algebra K k]

  E : WeierstrassCurve k
  [isElliptic : E.IsElliptic]

  normalised : ∀ a : 𝓞 K, a ≠ 0 → ∃ φ : Isogeny E E, invConst φ = algebraMap K k (a : K)

  periodLattice : (k →+* ℂ) → Submodule ℤ ℂ
  isPeriodLattice : ∀ s, IsPeriodLattice (E.map s) (periodLattice s)

attribute [instance] CMFamily.field CMFamily.numberField CMFamily.algebra CMFamily.isElliptic

variable [Algebra.IsQuadraticExtension ℚ K]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
