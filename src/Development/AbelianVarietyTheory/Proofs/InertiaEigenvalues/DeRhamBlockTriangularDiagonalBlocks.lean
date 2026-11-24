module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem exists_cols_isUnit {F : Type} [CommRing F] (hF : IsField F) {b n : Type} [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] (X : Matrix b n F) (Z : Matrix n b F) (h : X * Z = 1) :
    ∃ e : b → n, IsUnit (X.submatrix id e) := by
  letI : Field F := hF.toField
  have h1 : X.rank = Fintype.card b := by
    apply le_antisymm (Matrix.rank_le_card_height X)
    have := Matrix.rank_mul_le_left X Z
    rw [h, Matrix.rank_one] at this
    exact this
  have h2 : Module.finrank F (Submodule.span F (Set.range X.col)) = Fintype.card b := by
    exact (Matrix.finrank_span_range_col X).trans h1
  obtain ⟨κ, e, he, hspan, hli⟩ := exists_linearIndependent' F X.col
  haveI : Finite κ := Finite.of_injective e he
  letI : Fintype κ := Fintype.ofFinite κ
  have h3 : Fintype.card κ = Fintype.card b := by
    rw [← finrank_span_eq_card hli, hspan, h2]
  let τ : b ≃ κ := Fintype.equivOfCardEq h3.symm
  refine ⟨e ∘ τ, ?_⟩
  have h4 : LinearIndependent F (X.submatrix id (e ∘ τ)).col := hli.comp τ τ.injective
  exact Matrix.linearIndependent_cols_iff_isUnit.mp h4

end GlobalTheory.PMon.SubquotientAlgEquiv

end

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem map_mul_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p q s : Type}
    [Fintype q] (M : Matrix p q R) (N : Matrix q s R) : (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : R →+* R))

theorem map_one_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p : Type}
    [DecidableEq p] : (1 : Matrix p p R).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

end GlobalTheory.PMon.SubquotientAlgEquiv

namespace GlobalTheory.PMon

open scoped Matrix


open SubquotientAlgEquiv in
theorem subQuot : SubQuot := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c _ hblk hdr
  have hF := (_root_.GlobalTheory.PMon.bdR_tied l P AI T).1
  have e11 : ∀ m g (i j : a), matD P ρ m g (Sum.inl i) (Sum.inl j) = matD P ρ₁ m g i j := by
    intro m g i j; simp [matD, hblk g]
  have e21 : ∀ m g (i : b) (j : a), matD P ρ m g (Sum.inr i) (Sum.inl j) = 0 := by
    intro m g i j; simp [matD, hblk g]
  have e22 : ∀ m g (i j : b), matD P ρ m g (Sum.inr i) (Sum.inr j) = matD P ρ₂ m g i j := by
    intro m g i j; simp [matD, hblk g]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi := Units.mul_inv Q
    have hQiQ := Units.inv_mul Q
    have hinv : ∀ g : ↥(GK K), (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g) =
        (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g := by
      intro g
      have hs : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g) *
          (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g) = 1 := by
        rw [← map_mul_algEquiv, hQQi, map_one_algEquiv]
      calc (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g)
          = ((↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)) *
              (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g) := by
            rw [hQiQ, Matrix.one_mul]
        _ = (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
              (matD P ρ m g * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g)) *
              (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g) := by
            rw [hQ g]
        _ = (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g *
              ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g) *
              (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR g)) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hs, Matrix.mul_one]
    let Y := (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inl
    let W : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
    have hWY : W * Y = 1 := by
      rw [show W * Y = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inl Sum.inl from
        (Matrix.submatrix_mul _ _ Sum.inl id Sum.inl Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inl_injective
    have hYW : Yᵀ * Wᵀ = 1 := by rw [← Matrix.transpose_mul, hWY, Matrix.transpose_one]
    obtain ⟨e, he⟩ := exists_cols_isUnit hF Yᵀ Wᵀ hYW
    have hY' : IsUnit (Y.submatrix e id) := by
      have := (Matrix.isUnit_transpose _).2 he
      simpa [Matrix.transpose_submatrix] using this
    have hσY : ∀ g : ↥(GK K),
        (Y.submatrix e id).map (P.actQdR g) = Y.submatrix e id * matD P ρ₁ m g := by
      intro g; ext i j
      have := congrFun (congrFun (hinv g) (e i)) (Sum.inl j)
      simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e11, e21, mul_zero,
        Finset.sum_const_zero, add_zero] at this
      simpa [Y, Matrix.mul_apply] using this
    refine ⟨hY'.unit⁻¹, fun g => ?_⟩
    have hs : (↑hY'.unit : Matrix a a P.R.BdR).map (P.actQdR g) *
        (↑(hY'.unit⁻¹) : Matrix a a P.R.BdR).map (P.actQdR g) = 1 := by
      rw [← map_mul_algEquiv, Units.mul_inv, map_one_algEquiv]
    calc matD P ρ₁ m g * (↑(hY'.unit⁻¹) : Matrix a a P.R.BdR).map (P.actQdR g)
        = ((↑(hY'.unit⁻¹) : Matrix a a P.R.BdR) * (↑hY'.unit : Matrix a a P.R.BdR)) *
            matD P ρ₁ m g * (↑(hY'.unit⁻¹) : Matrix a a P.R.BdR).map (P.actQdR g) := by
          rw [Units.inv_mul, Matrix.one_mul]
      _ = (↑(hY'.unit⁻¹) : Matrix a a P.R.BdR) *
            ((↑hY'.unit : Matrix a a P.R.BdR) * matD P ρ₁ m g) *
            (↑(hY'.unit⁻¹) : Matrix a a P.R.BdR).map (P.actQdR g) := by
          simp only [Matrix.mul_assoc]
      _ = (↑(hY'.unit⁻¹) : Matrix a a P.R.BdR) *
            (↑hY'.unit : Matrix a a P.R.BdR).map (P.actQdR g) *
            (↑(hY'.unit⁻¹) : Matrix a a P.R.BdR).map (P.actQdR g) := by
          rw [hY'.unit_spec, hσY g]
      _ = _ := by rw [Matrix.mul_assoc, hs, Matrix.mul_one]
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi := Units.mul_inv Q
    let X : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
    let Z := (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr
    have hXZ : X * Z = 1 := by
      rw [show X * Z = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          (↑(Q⁻¹) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inr Sum.inr from
        (Matrix.submatrix_mul _ _ Sum.inr id Sum.inr Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inr_injective
    obtain ⟨e, he⟩ := exists_cols_isUnit hF X Z hXZ
    refine ⟨he.unit, fun g => ?_⟩
    rw [he.unit_spec]
    ext i j
    have := congrFun (congrFun (hQ g) (Sum.inr i)) (e j)
    simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e21, e22, zero_mul,
      Finset.sum_const_zero, zero_add] at this
    simpa [X, Matrix.mul_apply] using this

end GlobalTheory.PMon

end
