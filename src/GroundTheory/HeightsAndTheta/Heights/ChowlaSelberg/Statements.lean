import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian Filter Topology
open scoped nonZeroDivisors Real ModularForm UpperHalfPlane

noncomputable section

def eisensteinSum (Λ : Submodule ℤ ℂ) (n : ℕ) : ℂ := ∑' l : Λ, ((l : ℂ) ^ n)⁻¹

def latticeG₂ (Λ : Submodule ℤ ℂ) : ℂ := 60 * eisensteinSum Λ 4

def latticeG₃ (Λ : Submodule ℤ ℂ) : ℂ := 140 * eisensteinSum Λ 6

def latticeDiscr (Λ : Submodule ℤ ℂ) : ℂ := latticeG₂ Λ ^ 3 - 27 * latticeG₃ Λ ^ 2

theorem latticeDiscr_lattice (L : PeriodPair) : latticeDiscr L.lattice = discr L := rfl

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
