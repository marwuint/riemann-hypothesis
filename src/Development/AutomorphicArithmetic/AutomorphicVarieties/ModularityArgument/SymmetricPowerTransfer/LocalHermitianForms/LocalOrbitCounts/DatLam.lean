module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem ofE_mul {K : Type} [Field K] (Δ τ : K) (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

theorem UpperTheory.V.Z.Sym.Loc.datLam : UpperTheory.V.Z.Sym.Loc.DatLam := by
  intro K _ Δ τ c hreg hc lam hlam z hz
  show IsDat c (lam • ofE Δ (star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))) 1
  have hzu : (z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := z.mul_inv
  have hsz : star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
    rw [← star_mul, mul_comm _ (z : Etau K τ), hzu, star_one]
  generalize star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = w at hsz ⊢
  have hN : (z : Etau K τ) * star (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) := by
    rw [hz]
    ext <;> simp <;> ring
  have hzz : (z : Etau K τ) * (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) * ω := by
    rw [hz]
    ext <;> simp <;> ring
  have hzw : (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) * w := by
    rw [← hN, mul_assoc, hsz, mul_one]
  have hNu : IsUnit (algebraMap K (Etau K τ) (2 + τ)) :=
    isUnit_of_mul_isUnit_left (hzw ▸ z.isUnit)
  have ha : algebraMap K (Etau K τ) (2 + τ) * (w * w) = ω := by
    apply hNu.mul_left_cancel
    rw [← hzz, hzw]
    ring
  have hstarN : star (algebraMap K (Etau K τ) (2 + τ)) = algebraMap K (Etau K τ) (2 + τ) := by
    ext <;> simp
  have hs' : star (z : Etau K τ) = algebraMap K (Etau K τ) (2 + τ) * star w := by
    rw [hzw, star_mul', hstarN]
  have hb : algebraMap K (Etau K τ) (2 + τ) * (w * star w) = 1 := by
    rw [mul_left_comm, ← hs', mul_comm, hsz]
  have ofE_one : ofE Δ (1 : Etau K τ) = 1 := by
    ext <;> simp [ofE]
  have ofE_sm (r : K) (y : Etau K τ) :
      ofE Δ (algebraMap K (Etau K τ) r * y) = (algebraMap K (Lsq K Δ) r) • ofE Δ y := by
    ext <;> simp [ofE]
  have sig_ofE (y : Etau K τ) : sigL (ofE Δ y) = ofE Δ y := by
    ext <;> simp [sigL, ofE]
  have star_ofE (y : Etau K τ) : star (ofE Δ y) = ofE Δ (star y) := by
    ext <;> simp [ofE]
  have sig_sm (a : Lsq K Δ) (y : EL Δ τ) : sigL (a • y) = star a • sigL y := by
    ext <;> simp [sigL]
  have star_sm (a : Lsq K Δ) (y : EL Δ τ) : star (a • y) = a • star y := by
    ext <;> simp <;> ring
  have sig_one : sigL (1 : EL Δ τ) = 1 := by
    ext <;> simp [sigL]
  have hlam' : lam * star lam = algebraMap K (Lsq K Δ) (2 + τ) := by
    rw [← algebraMap_norm_eq_mul_star, hlam]
  refine ⟨hreg, hc, ?_, isUnit_one, ?_, ?_⟩
  · rw [sig_sm, sig_ofE, smul_mul_smul_comm, hlam', ← ofE_mul, ← ofE_sm, ha]
  · rw [sig_one, star_one]
  · rw [sig_one, one_mul, sig_sm, sig_ofE, star_sm, star_ofE, smul_mul_smul_comm, hlam',
      ← ofE_mul, ← ofE_sm, hb, ofE_one]
