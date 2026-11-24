module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.RealPar Matrix

namespace GlobalTheory.CoverExp

variable {p q : ℕ}

theorem sq_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    ((T.sq (T.expt X) : ℂˣ) : ℂ) = Complex.exp (X.trace / 2) := by
  apply GlobalTheory.FockDecay.sq_expt <;> assumption

theorem exists_expt_ker (hn : 1 ≤ p + q) (T : GrpData p q) :
    ∃ Z ∈ upq p q, T.cov (T.expt Z) = 1 ∧ T.sq (T.expt Z) = -1 := by
  let a : Ix p q := finSumFinEquiv.symm ⟨0, hn⟩
  refine ⟨TorusWt.torX (Pi.single a (2 * Real.pi)), TorusWt.torX_mem _, ?_, ?_⟩
  · apply Units.ext
    rw [T.expt_cov _ (TorusWt.torX_mem _), TorusWt.torX, Matrix.exp_diagonal, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext b
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    by_cases h : b = a
    · subst h
      simp [Complex.exp_two_pi_mul_I]
    · simp [h]
  · apply Units.ext
    rw [sq_expt T (TorusWt.torX_mem _), TorusWt.torX, Matrix.trace_diagonal, Finset.sum_eq_single a]
    · rw [Pi.single_eq_same, show ((2 * Real.pi : ℝ) : ℂ) * Complex.I / 2 = Real.pi * Complex.I by push_cast; ring,
        Complex.exp_pi_mul_I]
      simp
    · intro b _ h
      simp [h]
    · simp

theorem exists_blockOrd (p q : ℕ) : ∃ (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool), BlockOrd e ε := by
  refine ⟨finSumFinEquiv, fun i => (finSumFinEquiv.symm i).isLeft, fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) h
  · have h' : a < b := h
    exact h'
  · exact h.elim
  · exact h.elim
  · have h' : a < b := h
    exact Nat.add_lt_add_left h' p

theorem isPC_of_anticomm {X : Mat p q} (h : X * Jm p q = -(Jm p q * X)) : IsPC X := by
  intro a b hab
  have := congrFun (congrFun h a) b
  rw [Matrix.neg_apply, KStabLie.Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  rcases a with a | a <;> rcases b with b | b
  · simp only [Sum.elim_inl] at this
    linear_combination (1 / 2 : ℂ) * this
  · simp [sameBlock] at hab
  · simp [sameBlock] at hab
  · simp only [Sum.elim_inr] at this
    linear_combination (-1 / 2 : ℂ) * this

theorem exists_exp_mul_exp {g : Mat p q} (hg : gᴴ * Jm p q * g = Jm p q) :
    ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, g = NormedSpace.exp Z * NormedSpace.exp X := by
  obtain ⟨e, ε, hb⟩ := exists_blockOrd p q
  obtain ⟨Z, X, hZ, hX, h⟩ := Formalism.REAL.genExp_of Formalism.REAL.compact_exponential_surjective _ ε _ ((hb.inUJ_iff g).2 hg)
  obtain ⟨Z, rfl⟩ := (Matrix.reindex e e).surjective Z
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective X
  have hG : ∀ Y : Mat p q, Formalism.REAL.inG ε (Matrix.reindex e e Y) → Y ∈ upq p q := by
    intro Y h1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rwa [Matrix.submatrix_add]
  have hexp : ∀ Y : Mat p q, NormedSpace.exp (Matrix.reindex e e Y) = Matrix.reindex e e (NormedSpace.exp Y) := by
    intro Y
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) Y).symm
  refine ⟨Z, hG Z hZ.1, (KStabLie.isKC_iff Z).2 ?_, X, ⟨hG X hX.1, isPC_of_anticomm ?_⟩, ?_⟩
  · have h2 := hZ.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h2
  · have h2 := hX.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h2
    exact h2
  · rw [hexp, hexp] at h
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h

theorem closure_expt_eq_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q,
    Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  intro p q hn T
  have key : ∀ g : T.G, ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, T.cov g = T.cov (T.expt Z) * T.cov (T.expt X) := by
    intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := exists_exp_mul_exp ((mem_Upq _).1 (T.cov_mem g))
    exact ⟨Z, hZ, hK, X, hX, Units.ext (by rw [Units.val_mul, T.expt_cov Z hZ, T.expt_cov X hX.1, h])⟩
  constructor
  · rw [eq_top_iff]
    intro g _
    obtain ⟨Z, hZ, -, X, hX, h⟩ := key g
    obtain ⟨C, hC, hC1, hC2⟩ := exists_expt_ker hn T
    have hm : ∀ Y ∈ upq p q, T.expt Y ∈ Subgroup.closure (T.expt '' upq p q) :=
      fun Y hY => Subgroup.subset_closure ⟨Y, hY, rfl⟩
    have hx := Subgroup.mul_mem _ (hm Z hZ) (hm X hX.1)
    rw [← map_mul] at h
    set x := T.expt Z * T.expt X
    have h2 : ((T.sq g : ℂˣ) : ℂ) ^ 2 = ((T.sq x : ℂˣ) : ℂ) ^ 2 := by rw [T.sq_sq, T.sq_sq, h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · rwa [Cover.ext_of h (Units.ext h3)]
    · have : g = T.expt C * x := Cover.ext_of (by rw [map_mul, hC1, one_mul, h])
        (Units.ext (by rw [map_mul, hC2, h3]; simp))
      rw [this]
      exact Subgroup.mul_mem _ (hm C hC) hx
  · intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := key g
    refine ⟨g * (T.expt X)⁻¹, ?_, X, hX, by simp⟩
    have h1 := KStabLie.expt_mem T hZ hK 1
    rw [one_smul] at h1
    change IsKC _
    rwa [map_mul, map_inv, h, mul_inv_cancel_right]

end GlobalTheory.CoverExp

end
