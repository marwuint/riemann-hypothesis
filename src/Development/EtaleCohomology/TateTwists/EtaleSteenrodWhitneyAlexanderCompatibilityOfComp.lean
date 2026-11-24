module

public import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Finsupp.Pointwise

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds, Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta, Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit, Development.EtaleCohomology.TateTwists.LeafAcycPf, Development.EtaleCohomology.TateTwists.LeafAwPf, Development.EtaleCohomology.TateTwists.LeafWaPf, Development.EtaleCohomology.TateTwists.EtaleSteenrodWhitneyAlexanderCompatibilityOfComp

-- ===== clump member: Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_push {N M K : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M)
    (θ' : SimplexCategory.mk M ⟶ SimplexCategory.mk K) (c : Pr N →₀ ℤ) :
    Pr.push θ' (Pr.push θ c) = Pr.push (θ ≫ θ') c := by
  simp only [Pr.push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  rfl

def inv {N : ℕ} (p : Fin (N + 3) × Fin (N + 2)) : Fin (N + 3) × Fin (N + 2) :=
  if h : (p.2 : ℕ) < p.1 then (p.2.castSucc, p.1.pred (by intro e; rw [e] at h; simp at h))
  else (p.2.succ, p.1.castPred (fun e => by have := congrArg Fin.val e; have := p.2.isLt; simp at this; simp at *; omega))

theorem prism_boundary_map_square_zero_holds : leaf_bdbd := by
  intro N c
  unfold Pr.bd

  simp only [map_sum, map_zsmul, push_push, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_product' (f := fun (i : Fin (N + 3)) (j : Fin (N + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • Pr.push (SimplexCategory.δ j ≫ SimplexCategory.δ i) c)]
  refine Finset.sum_involution (fun p _ => inv p) ?_ ?_ (fun p _ => by simp) ?_
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h
    · have hj : j ≤ i.pred (fun e => by subst e; simp at h) := by
        rw [Fin.le_def, Fin.val_pred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      have hi : (i.pred (fun e => by subst e; simp at h)).succ = i := Fin.succ_pred _ _
      rw [hi] at e
      simp only [Fin.val_castSucc, Fin.val_pred]
      rw [e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨i - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]; ring
    · push Not at h
      have hne : i ≠ Fin.last (N + 2) := fun e => by have := congrArg Fin.val e; have := j.isLt; simp at this; simp at *; omega
      have hj : i.castPred hne ≤ j := by rw [Fin.le_def, Fin.coe_castPred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      rw [Fin.castSucc_castPred] at e
      simp only [Fin.val_succ, Fin.coe_castPred]
      rw [← e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      rw [pow_succ]; ring
  · rintro ⟨i, j⟩ - -
    simp only [inv]
    split_ifs with h <;> intro e <;> simp [Prod.ext_iff, Fin.ext_iff] at e <;> omega
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h h2 h2
    · exfalso; simp at h2; omega
    · simp
    · simp
    · exfalso; simp at h2; omega

end LateralTheory.EtaleFoundations.SteenPf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_d₁ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₁ = Pr.d₁ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases p with
  | zero => simp [Pr.d₁]
  | succ p =>

    simp only [Pr.d₁, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_d₂ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₂ = Pr.d₂ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases r with
  | zero => simp [Pr.d₂]
  | succ r =>

    simp only [Pr.d₂, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_single {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) (n : ℤ) :
    Pr.push θ (Finsupp.single z n) = Finsupp.single ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ n := by
  simp [Pr.push]

lemma d_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c) := by
  have : (Pr.d M).comp (Pr.push θ) = (Pr.push θ).comp (Pr.d N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, push_single, Pr.d, Finsupp.linearCombination_single, map_smul,
      map_add, push_d₁, push_d₂]
  exact LinearMap.congr_fun this c

theorem steenrod_prism_chain_differential_squared_eq_zero_of_etale : leaf_dbd := by
  intro N c
  unfold Pr.bd

  simp only [map_sum, map_zsmul, d_push]

end LateralTheory.EtaleFoundations.SteenPf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations\npublic import Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds\npublic import Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section


open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney (hA : leaf_acyc) (hAW : leaf_aw) (hWA : leaf_wa) :
    LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy :=
  LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations hA steenrod_prism_chain_differential_squared_eq_zero_of_etale prism_boundary_map_square_zero_holds hAW hWA
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.LeafAcycPf =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.LeafAcycPf", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.AcycPf

def cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun i => Fin.cases 0 (fun j => a.toOrderHom j) i, by
    intro i j h
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp)
      | succ j => simpa using a.toOrderHom.monotone (Fin.succ_le_succ_iff.1 h)⟩

def v0 {N : ℕ} : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

lemma δ0_cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 0 ≫ cone a = a := by
  ext j
  simp [SimplexCategory.δ, cone]

lemma δsucc_cone {p N : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (i : Fin (p + 2)) :
    SimplexCategory.δ i.succ ≫ cone a = cone (SimplexCategory.δ i ≫ a) := by
  ext j
  induction j using Fin.cases with
  | zero => simp [SimplexCategory.δ, cone]
  | succ j => simp [SimplexCategory.δ, cone, Fin.succ_succAbove_succ]

lemma δ1_cone {N : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 1 ≫ cone a = v0 := by
  ext j
  fin_cases j
  simp [SimplexCategory.δ, cone, v0]
  rfl

abbrev X {N : ℕ} (p r : ℕ) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) : Pr N →₀ ℤ :=
  Finsupp.single (⟨p, r, a, b⟩ : Pr N) 1

def Hg {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  X (z.1 + 1) z.2.1 (cone z.2.2.1) z.2.2.2 + if z.1 = 0 then X 0 (z.2.1 + 1) v0 (cone z.2.2.2) else 0

def H (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ Hg

lemma d_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d N (X p r a b) = Pr.d₁ (⟨p, r, a, b⟩ : Pr N) + (-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N) := by
  simp [Pr.d, X]

lemma H_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    H N (X p r a b) = Hg (⟨p, r, a, b⟩ : Pr N) := by
  simp [H, X]

lemma Hg_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨0, r, a, b⟩ : Pr N) = X 1 r (cone a) b + X 0 (r + 1) v0 (cone b) := by
  simp [Hg]

lemma Hg_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨p + 1, r, a, b⟩ : Pr N) = X (p + 2) r (cone a) b := by
  simp [Hg]

lemma diffOne_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_second_face_of_vertex_eq_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_first_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X p r (SimplexCategory.δ i ≫ a) b := by
  simp [Pr.d₁, X]

lemma simplex_pair_second_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) = ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p r a (SimplexCategory.δ i ≫ b) := by
  simp [Pr.d₂, X]

lemma simplex_pair_first_face_cone_vertex_formula {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨1, r, cone a, b⟩ : Pr N) = X 0 r a b - X 0 r v0 b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_two]
  have h1 : SimplexCategory.δ (1 : Fin 2) ≫ cone a = v0 := δ1_cone a
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, δ0_cone, h1, neg_smul, sub_eq_add_neg]

lemma simplex_pair_first_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 2, r, cone a, b⟩ : Pr N) = X (p + 1) r a b - ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X (p + 1) r (cone (SimplexCategory.δ i ≫ a)) b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma simplex_pair_second_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1 + 1, a, cone b⟩ : Pr N) = X p (r + 1) a b - ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p (r + 1) a (cone (SimplexCategory.δ i ≫ b)) := by
  rw [simplex_pair_second_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma alt_const {N : ℕ} (p : ℕ) (Y : Pr N →₀ ℤ) :
    ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (if p = 0 then Y else 0) = 0 := by
  cases p with
  | zero => simp [Fin.sum_univ_two]
  | succ p => simp

lemma key {N : ℕ} (z : Pr N) (hz : z.1 + z.2.1 ≠ 0) :
    Pr.d N (H N (Finsupp.single z 1)) + H N (Pr.d N (Finsupp.single z 1)) = Finsupp.single z 1 := by
  obtain ⟨p, r, a, b⟩ := z
  change Pr.d N (H N (X p r a b)) + H N (Pr.d N (X p r a b)) = X p r a b
  cases p with
  | zero =>
    cases r with
    | zero => simp at hz
    | succ r =>
      rw [H_X, Hg_zero, map_add (f := _), d_X, d_X, d_X, simplex_pair_first_face_cone_vertex_formula, diffOne_zero, diffOne_zero, simplex_pair_second_face_cone_succ_formula, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]

      simp only [map_sum, map_zsmul, H_X, Hg_zero, smul_add, Finset.sum_add_distrib, zero_add,
      pow_zero, pow_one, one_smul, neg_smul]
      abel
  | succ p =>
    cases r with
    | zero =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_of_vertex_eq_zero, simplex_pair_second_face_of_vertex_eq_zero]

      simp only [map_sum, map_zsmul, H_X, smul_zero, add_zero]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      abel
    | succ r =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]

      simp only [map_add (f := _), map_sum, map_zsmul, H_X, Hg_succ]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      have e : (-1 : ℤ) ^ (p + 2) = -(-1) ^ (p + 1) := by ring
      rw [e, neg_smul]
      abel

lemma deg_H {N k : ℕ} {c : Pr N →₀ ℤ} (hdeg : Pr.Deg (k + 1) c) : Pr.Deg (k + 2) (H N c) := by
  intro z hz
  have e : H N c = ∑ y ∈ c.support, c y • Hg y := by
    simp [H, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [e] at hz
  obtain ⟨y, hy, hz2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have hz3 := Finsupp.support_smul hz2
  have hy' := hdeg y hy
  obtain ⟨p, r, a, b⟩ := y
  simp only [Hg] at hz3
  rcases Finset.mem_union.1 (Finsupp.support_add hz3) with h | h
  · have := Finsupp.support_single_subset h
    rw [Finset.mem_singleton] at this
    subst this
    change p + r = k + 1 at hy'
    change p + 1 + r = k + 2
    omega
  · split_ifs at h with hp
    · have := Finsupp.support_single_subset h
      rw [Finset.mem_singleton] at this
      subst this
      change p + r = k + 1 at hy'
      change 0 + (r + 1) = k + 2
      omega
    · simp at h

end LateralTheory.EtaleFoundations.AcycPf


open LateralTheory.EtaleFoundations.AcycPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  intro N k c hdeg hcyc
  refine ⟨LateralTheory.EtaleFoundations.AcycPf.H N c, LateralTheory.EtaleFoundations.AcycPf.deg_H hdeg, ?_⟩
  have h : ∀ y ∈ c.support, Pr.d N (LateralTheory.EtaleFoundations.AcycPf.H N (Finsupp.single y (c y))) + LateralTheory.EtaleFoundations.AcycPf.H N (Pr.d N (Finsupp.single y (c y))) =
      Finsupp.single y (c y) := by
    intro y hy
    have hy' := hdeg y hy
    rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← smul_add, LateralTheory.EtaleFoundations.AcycPf.key y (by omega)]
  have e : Pr.d N (LateralTheory.EtaleFoundations.AcycPf.H N c) + LateralTheory.EtaleFoundations.AcycPf.H N (Pr.d N c) = c := by
    conv_rhs => rw [← Finsupp.sum_single c]
    conv_lhs => rw [← Finsupp.sum_single c]

    simpa only [Finsupp.sum, map_sum, ← Finset.sum_add_distrib] using Finset.sum_congr rfl h
  rwa [hcyc, map_zero, add_zero] at e

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.LeafAcycPf =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.LeafAwPf =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.LeafAwPf", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwPf

abbrev sb {n : ℕ} (j l : ℕ) (h : j + l ≤ n) : SimplexCategory.mk l ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval j l h

@[simp] lemma sb_apply {n : ℕ} (j l : ℕ) (h : j + l ≤ n) (i : Fin (l + 1)) :
    (((sb j l h).toOrderHom i : Fin (n + 1)) : ℕ) = i + j := rfl

lemma m_last (p r : ℕ) (h1 : 0 + (p + 1) ≤ p + r + 1) (h2 : 0 + p ≤ p + r + 1) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ sb 0 (p + 1) h1 = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, sb_apply]

lemma m_zero (p r : ℕ) (h1 : p + (r + 1) ≤ p + r + 1) (h2 : (p + 1) + r ≤ p + r + 1) :
    SimplexCategory.δ 0 ≫ sb p (r + 1) h1 = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_lo (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + (p + 1) ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k, by omega⟩ : Fin (p + 2)) ≫ sb 0 (p + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [sb_apply])

lemma simplex_subinterval_back_comp_face_within_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : p + r ≤ p + r)
    (h2 : (p + 1) + r ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [sb_apply])
  all_goals omega

lemma m_hi (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + p ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_above_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : p + r ≤ p + r)
    (h2 : p + (r + 1) ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k - p, by omega⟩ : Fin (r + 2)) ≫ sb p (r + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [sb_apply])
  all_goals omega

def T (n p r : ℕ) (h : p + r ≤ n) : Pr n := ⟨p, r, sb 0 p (by omega), sb p r h⟩

noncomputable def S (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Finsupp.single (T n x.1 x.2 h) 1 else 0

noncomputable def g1 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Pr.d₁ (T n x.1 x.2 h) else 0

noncomputable def g2 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then (-1 : ℤ) ^ x.1 • Pr.d₂ (T n x.1 x.2 h) else 0

lemma aw_eq (n : ℕ) : Pr.aw n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, S n x := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range (fun k => S n (k, n - k))]
  unfold Pr.aw
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.isLt
  simp only [S]
  rw [dite_eq_left (by omega)]
  rfl

lemma bd_sum {N : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Pr N →₀ ℤ) :
    Pr.bd (∑ x ∈ s, g x) = ∑ x ∈ s, Pr.bd (g x) := by
  unfold Pr.bd

  simpa only [map_sum, Finset.smul_sum] using Finset.sum_comm

lemma d_S (n : ℕ) (x : ℕ × ℕ) : Pr.d n (S n x) = g1 n x + g2 n x := by
  unfold S g1 g2
  split_ifs with h
  · simp only [Pr.d, Finsupp.linearCombination_single, one_smul]
    rfl
  · simp

lemma split_sum {M : Type*} [AddCommMonoid M] (p r : ℕ) (f : Fin (p + r + 2) → M) :
    ∑ k, f k = ∑ i : Fin (p + 1), f ⟨i, by omega⟩ + ∑ j : Fin (r + 1), f ⟨p + 1 + j, by omega⟩ := by
  rw [← (finCongr (by omega : (p + 1) + (r + 1) = p + r + 2)).sum_comp, Fin.sum_univ_add]
  rfl

lemma bd_single (n : ℕ) (z : Pr n) : Pr.bd (Finsupp.single z 1) =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • Finsupp.single
      (⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ k, z.2.2.2 ≫ SimplexCategory.δ k⟩ : Pr (n + 1)) 1 := by
  unfold Pr.bd
  simp [Pr.push]

lemma key (p r : ℕ) :
    Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) + (-1 : ℤ) ^ p • Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) =
      Pr.bd (Finsupp.single (T (p + r) p r le_rfl) 1) := by
  have e1 : Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) = ∑ i : Fin (p + 2),
      Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (i : ℕ)) := rfl
  have e2 : Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) = ∑ j : Fin (r + 2),
      Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (j : ℕ)) := rfl
  rw [e1, e2, bd_single, split_sum, Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1)]
  have hlo : ∀ i : Fin (p + 1),
      (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      Finsupp.single (⟨p, r, SimplexCategory.δ i.castSucc ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.castSucc i : Fin (p + 2)) : ℕ)) := by
    intro i
    have hi := i.isLt
    simp only [T]
    rw [m_lo p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega), simplex_subinterval_back_comp_face_within_front p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega),
      Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  have hhi : ∀ j : Fin (r + 1),
      (-1 : ℤ) ^ (p + 1 + (j : ℕ)) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j.succ ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.succ j : Fin (r + 2)) : ℕ)) := by
    intro j
    have hj := j.isLt
    simp only [T]
    rw [m_hi p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega), simplex_subinterval_back_comp_face_above_front p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega),
      Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]
    have hf : (⟨p + 1 + (j : ℕ) - p, by omega⟩ : Fin (r + 2)) = j.succ := by
      ext; simp; omega
    rw [hf, Fin.val_succ]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => hlo i), Finset.sum_congr rfl (fun j _ => hhi j), ← Finset.smul_sum,
    m_last p r (by omega) (by omega), m_zero p r (by omega) (by omega), smul_add]
  have hc : Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ)) +
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ)) = 0 := by
    rw [Finsupp.smul_single, ← Finsupp.single_add]
    simp [pow_succ]
  apply eq_of_sub_eq_zero
  rw [← hc]
  abel

theorem leaf_aw_of : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  intro N

  rw [aw_eq, aw_eq, map_sum, bd_sum]
  simp only [d_S]
  rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  have z1 : g1 (N + 1) (0, N + 1) = 0 := by
    unfold g1; rw [dite_eq_left (by simp)]; rfl
  have z2 : g2 (N + 1) (N + 1, 0) = 0 := by
    unfold g2; rw [dite_eq_left (by simp)]
    exact smul_zero _
  rw [z1, z2, zero_add, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨p, r⟩ := x
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  simp only at hx
  subst hx
  unfold g1 g2 S
  rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega), dite_eq_left (by simp)]
  exact key p r

end LateralTheory.EtaleFoundations.AwPf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.LeafAwPf =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.LeafWaPf =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.LeafWaPf", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.Finsupp.Pointwise\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf.WaPf

def swap {N : ℕ} (z : Pr N) : Pr N := ⟨z.2.1, z.1, z.2.2.2, z.2.2.1⟩

noncomputable def tau (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z => Finsupp.single (swap z) ((-1 : ℤ) ^ (z.1 * z.2.1))

lemma tau_single {N : ℕ} (z : Pr N) (n : ℤ) :
    tau N (Finsupp.single z n) = Finsupp.single (swap z) (n * (-1 : ℤ) ^ (z.1 * z.2.1)) := by
  simp [tau, Finsupp.linearCombination_single, Finsupp.smul_single]

lemma d_single {N : ℕ} (z : Pr N) (n : ℤ) :
    Pr.d N (Finsupp.single z n) = n • (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  simp [Pr.d, Finsupp.linearCombination_single]

lemma d_tau_single {N : ℕ} (z : Pr N) :
    Pr.d N (tau N (Finsupp.single z 1)) = tau N (Pr.d N (Finsupp.single z 1)) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [tau_single, d_single, d_single]
  cases p with
  | zero =>
    cases r with
    | zero => simp [swap, Pr.d₁, Pr.d₂]
    | succ r =>

      simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_smul, map_sum, tau_single, Finset.smul_sum,
      Finsupp.smul_single, smul_eq_mul]
      simp
  | succ p =>
    cases r with
    | zero =>

      simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_smul, map_sum, tau_single, Finset.smul_sum,
      Finsupp.smul_single, smul_eq_mul]
      simp
    | succ r =>

      simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_sum, tau_single, Finset.smul_sum,
      Finsupp.smul_single, smul_eq_mul, smul_add]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf
        (try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])
        (try exact neg_one_pow_eq_or ℤ _)
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf

lemma d_tau {N : ℕ} (c : Pr N →₀ ℤ) : Pr.d N (tau N c) = tau N (Pr.d N c) := by
  have : (Pr.d N).comp (tau N) = (tau N).comp (Pr.d N) := by
    exact Finsupp.lhom_ext' fun z => LinearMap.ext_ring (d_tau_single z)
  exact LinearMap.congr_fun this c

lemma tau_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    tau M (Pr.push θ c) = Pr.push θ (tau N c) := by
  have : (tau M).comp (Pr.push θ) = (Pr.push θ).comp (tau N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tau_single]
    rfl
  exact LinearMap.congr_fun this c

lemma tau_bd {N : ℕ} (c : Pr N →₀ ℤ) : tau (N + 1) (Pr.bd c) = Pr.bd (tau N c) := by
  unfold Pr.bd

  simp only [map_sum, map_zsmul, tau_push]

lemma wa_eq (N : ℕ) : Pr.wa N = tau N (Pr.aw N) := by
  unfold Pr.wa Pr.aw

  simp only [map_sum, tau_single, swap, one_mul]

end LateralTheory.EtaleFoundations.SteenPf.WaPf


open LateralTheory.EtaleFoundations.SteenPf LateralTheory.EtaleFoundations.SteenPf.WaPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of_aw (hAW : leaf_aw) : leaf_wa := by
  intro N
  rw [wa_eq, wa_eq, d_tau, hAW, tau_bd]


end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.LeafWaPf =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleSteenrodWhitneyAlexanderCompatibilityOfComp =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleSteenrodWhitneyAlexanderCompatibilityOfComp", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations\npublic import Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit\npublic import Development.EtaleCohomology.TateTwists.LeafAcycPf\npublic import Development.EtaleCohomology.TateTwists.LeafAwPf\npublic import Development.EtaleCohomology.TateTwists.LeafWaPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
theorem etale_steenrod_whitney_alexander_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_wa := by
  apply _root_.LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of_aw <;> first | exact _root_.LateralTheory.EtaleFoundations.AwPf.leaf_aw_of
theorem etale_steenrod_power_operation_properties_of_components : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  apply LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney <;> first | exact _root_.LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of | exact _root_.LateralTheory.EtaleFoundations.AwPf.leaf_aw_of | exact etale_steenrod_whitney_alexander_compatibility_of_components
alias intersectionNumber_baseChange := _root_.LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy.etale_steenrod_power_operation_properties_of_components
end LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleSteenrodWhitneyAlexanderCompatibilityOfComp =====
