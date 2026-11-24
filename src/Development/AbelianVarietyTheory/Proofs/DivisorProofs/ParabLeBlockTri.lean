module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def natBlocks (b : Fin r → Fin s) : Fin r → ℕ := fun i => (b i : ℕ)

theorem blockTri_le_parab (b : Fin r → Fin s) : blockTri (κ := K) (natBlocks b) ≤ parab K b := by
  intro p hp
  refine ⟨fun i j hij => hp hij, fun i j hij => ?_⟩
  exact (inv_mem hp : p⁻¹ ∈ blockTri (κ := K) (natBlocks b)) hij

theorem parab_le_blockTri (b : Fin r → Fin s) : parab K b ≤ blockTri (κ := K) (natBlocks b) := by
  exact fun p hp i j hij => hp.1 i j hij

theorem levi_one (b : Fin r → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  exact Units.ext (Matrix.submatrix_one _ Subtype.val_injective)

theorem levi_mul (b : Fin r → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := Units.ext (blk_mul b c p.2.1 q.2.1)

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

def leviTensor : Representation ℂ (blockTri (κ := K) (natBlocks b))
    (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam (Subgroup.inclusion (blockTri_le_parab b) p)
  map_one' := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) 1)) = LinearMap.id := by
      intro c
      rw [map_one, levi_one, map_one]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_id
  map_mul' p q := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) (p * q))) =
        (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) ∘ₗ
          (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) q)) := by
      intro c
      rw [map_mul, levi_mul, map_mul]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_comp _ _

theorem leviTensor_apply (p : blockTri (κ := K) (natBlocks b)) :
    leviTensor b lam p = PiTensorProduct.map (fun c =>
      (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p))) := rfl

instance finiteTensor : FiniteDimensional ℂ (PiTensorProduct ℂ (fun c => (lam c : Type))) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c : Type))

end GlobalTheory.HcIrr
