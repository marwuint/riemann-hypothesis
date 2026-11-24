module

public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Mathlib.RepresentationTheory.Invariants
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.SerBridgeGLW

theorem trace_piTensorMap {s : ℕ} {M : Fin s → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let b := fun c => Module.Free.chooseBasis ℂ (M c)
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ i, (b c).repr (f c (b c i)) i := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (b c)]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [LinearMap.trace_eq_matrix_trace ℂ (Basis.piTensorProduct b)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]

theorem levi_mul' (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  show blk K b c (((p * q : parab K b) : GL ι K) : Matrix ι ι K) =
    blk K b c ((p : GL ι K) : Matrix ι ι K) * blk K b c ((q : GL ι K) : Matrix ι ι K)
  rw [← blk_mul b c p.2.1 q.2.1]
  rfl

theorem levi_one' (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  exact Units.ext (Matrix.submatrix_one _ Subtype.val_injective)

def inflRep (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) :
    Representation ℂ (parab K b) (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam p
  map_one' := by
    simp only [infl, levi_one', map_one]
    exact PiTensorProduct.map_one
  map_mul' p q := by
    simp only [infl, levi_mul', map_mul]
    exact PiTensorProduct.map_mul _ _

theorem mem_inv_linHom_iff {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) (f : V →ₗ[ℂ] W) :
    f ∈ (Representation.linHom ρV ρW).invariants ↔ ∀ g, f ∘ₗ ρV g = ρW g ∘ₗ f := by
  rw [Representation.mem_invariants]
  constructor
  · intro h g
    ext x
    have := congrArg (fun φ : V →ₗ[ℂ] W => φ (ρV g x)) (h g)
    simp only [Representation.linHom_apply, LinearMap.comp_apply, Representation.inv_self_apply] at this
    simpa only [LinearMap.comp_apply] using this.symm
  · intro h g
    ext x
    have := congrArg (fun φ : V →ₗ[ℂ] W => φ (ρV g⁻¹ x)) (h g)
    simp only [LinearMap.comp_apply, Representation.self_inv_apply] at this
    simpa only [Representation.linHom_apply, LinearMap.comp_apply] using this.symm

end PI.SerBridgeGLW
