module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Instances.Matrix
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
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

open MvPolynomial

namespace GlobalTheory.SubstCoeff

variable {σ : Type}

theorem continuous_coeff_mul {Y : Type} [TopologicalSpace Y] (F G : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (F y) m) (hG : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (G y) m) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (F y * G y) m := by
  classical
  simp only [coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hF _).mul (hG _)

theorem continuous_coeff_pow {Y : Type} [TopologicalSpace Y] (F : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (F y) m) (e : ℕ) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (F y ^ e) m := by
  induction e generalizing m with
  | zero =>
    classical
    simpa only [pow_zero, coeff_one] using continuous_const
  | succ e ih =>
    simpa only [pow_succ] using continuous_coeff_mul _ _ ih hF m

theorem continuous_coeff_prod {Y κ : Type} [TopologicalSpace Y] (s : Finset κ) (f : κ → Y → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (f q y) m) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (∏ q ∈ s, f q y) m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    simpa only [Finset.prod_empty, coeff_one] using continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact continuous_coeff_mul _ _ (hf a (Finset.mem_insert_self a s))
      (fun m' => ih (fun q hq => hf q (Finset.mem_insert_of_mem hq)) m') m

theorem isAlgebraic_sum {κ : Type} (s : Finset κ) (f : κ → ℂ) (hf : ∀ q ∈ s, IsAlgebraic ℚ (f q)) :
    IsAlgebraic ℚ (∑ q ∈ s, f q) :=
  Finset.sum_induction f (IsAlgebraic ℚ) (fun _ _ ha hb => ha.add hb) isAlgebraic_zero hf

theorem isAlgebraic_coeff_mul (P Q : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m)) (hQ : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff Q m)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (P * Q) m) := by
  classical
  rw [coeff_mul]
  exact isAlgebraic_sum _ _ fun x _ => (hP _).mul (hQ _)

theorem isAlgebraic_coeff_one (m : σ →₀ ℕ) : IsAlgebraic ℚ (AddMonoidAlgebra.coeff (1 : MvPolynomial σ ℂ) m) := by
  classical
  rw [coeff_one]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem isAlgebraic_coeff_pow (P : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m)) (e : ℕ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (P ^ e) m) := by
  induction e generalizing m with
  | zero => simpa only [pow_zero] using isAlgebraic_coeff_one m
  | succ e ih =>
    rw [pow_succ]
    exact isAlgebraic_coeff_mul _ _ ih hP m

theorem isAlgebraic_coeff_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff (f q) m)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (∏ q ∈ s, f q) m) :=
  Finset.prod_induction f (fun P => ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m))
    (fun _ _ ha hb => isAlgebraic_coeff_mul _ _ ha hb) isAlgebraic_coeff_one hf m

variable {ι : Type} {N n : ℕ}

theorem substF_monomial_one (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF h g (monomial k 1) = ∏ q ∈ k.support, (GlobalTheory.CompactHowe.substF h g (X q)) ^ k q := by
  rw [monomial_eq, map_mul, C_1, map_one, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow]

theorem continuous_coeff_substF_X (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    Continuous fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) =>
      AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (X q)) m := by
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  refine Continuous.mul (Continuous.mul ?_ ?_) continuous_const
  · exact ((continuous_apply q.1).comp continuous_fst).matrix_elem a q.2.1
  · exact ((continuous_apply q.1).comp continuous_snd).matrix_elem b q.2.2

theorem isAlgebraic_coeff_substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hh : ∀ i a b, IsAlgebraic ℚ (h i a b)) (hg : ∀ i a b, IsAlgebraic ℚ (g i a b))
    (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (X q)) m) := by
  classical
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine isAlgebraic_sum _ _ fun a _ => isAlgebraic_sum _ _ fun b _ => ?_
  refine ((hh _ _ _).mul (hg _ _ _)).mul ?_
  rw [coeff_X']
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem coeff_substF_monomial_continuous_algebraic :
    ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  intro ι N n k k'
  refine ⟨?_, fun h g hh hg => ?_⟩
  · simp only [substF_monomial_one]
    exact continuous_coeff_prod _ _ (fun q _ m => continuous_coeff_pow _ (continuous_coeff_substF_X q) _ m) k'
  · rw [substF_monomial_one]
    exact isAlgebraic_coeff_prod _ _
      (fun q _ m => isAlgebraic_coeff_pow _ (isAlgebraic_coeff_substF_X h g hh hg q) _ m) k'

end GlobalTheory.SubstCoeff
