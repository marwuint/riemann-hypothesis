module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

private def derivationCompAlgebraMap (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k T T) :
    Derivation k S T :=
  Derivation.mk' (D.toLinearMap.comp (IsScalarTower.toAlgHom k S T).toLinearMap) (by
    intro a b
    show D (algebraMap S T (a * b)) = a • D (algebraMap S T b) + b • D (algebraMap S T a)
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def])

private theorem derivation_comp_algebraMap_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k T T) (s : S) :
    derivationCompAlgebraMap k S T D s = D (algebraMap S T s) := rfl

private def algebraMapCompDerivation (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k S S) :
    Derivation k S T :=
  Derivation.mk' ((IsScalarTower.toAlgHom k S T).toLinearMap.comp D.toLinearMap) (by
    intro a b
    show algebraMap S T (D (a * b)) = a • algebraMap S T (D b) + b • algebraMap S T (D a)
    rw [D.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, Algebra.smul_def,
      Algebra.smul_def])

private theorem algebraMap_comp_derivation_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k S S) (s : S) :
    algebraMapCompDerivation k S T D s = algebraMap S T (D s) := rfl

theorem derivation_ext_of_coord (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
    [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (M : Type*) [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (D₁ D₂ : Derivation k S M)
    (h : ∀ i : ι, D₁ (coord k ι S i) = D₂ (coord k ι S i)) : D₁ = D₂ := by
  have key : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    refine (basisKaehler k ι S).ext ?_
    intro i
    rw [basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  refine Derivation.ext fun x => ?_
  rw [← Derivation.liftKaehlerDifferential_comp_D D₁ x,
    ← Derivation.liftKaehlerDifferential_comp_D D₂ x, key]

theorem partialDeriv_inr_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (j : κ) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inr j) (algebraMap S T s) = 0 := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inr j)) = 0 := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro i
    rw [derivation_comp_algebraMap_apply, hcoord i,
      partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inr j) (Sum.inl i) (by simp)]
    have h0 : ((0 : Derivation k S T)) (coord k ι S i) = 0 := rfl
    rw [h0]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply] at h2
  have h0 : ((0 : Derivation k S T)) s = 0 := rfl
  rw [h0] at h2
  exact h2

theorem partialDeriv_inl_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (i : ι) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inl i))
      = algebraMapCompDerivation k S T (partialDeriv k ι S i) := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro j
    rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply, hcoord j]
    by_cases hij : i = j
    · subst hij
      rw [partialDeriv_coord_self, partialDeriv_coord_self, map_one]
    · rw [partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inl i) (Sum.inl j) (by simpa using hij),
        partialDeriv_coord_of_ne k ι S i j hij, map_zero]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply] at h2
  exact h2

theorem map_derivIdeal_sum (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (J : Ideal S) :
    Ideal.map (algebraMap S T) (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S T) J) := by
  have key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J →
      algebraMap S T (D y) ∈ derivIdeal k (Ideal.map (algebraMap S T) J) := by
    intro D y hy
    have hsp : D ∈ Submodule.span S (Set.range (partialDeriv k ι S)) :=
      span_range_partialDeriv k ι S ▸ Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨i, rfl⟩ := hD
        rw [← partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
        exact derivation_apply_mem_derivIdeal k _ _ (Ideal.mem_map_of_mem _ hy)
    | zero =>
        rw [zero_apply, map_zero]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        rw [add_apply, map_add (f := _)]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        rw [smul_apply, smul_eq_mul, map_mul]
        exact Ideal.mul_mem_left _ _ ha
  have key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J →
      D' (algebraMap S T y) ∈ Ideal.map (algebraMap S T) (derivIdeal k J) := by
    intro D' y hy
    have hsp : D' ∈ Submodule.span T (Set.range (partialDeriv k (ι ⊕ κ) T)) :=
      span_range_partialDeriv k (ι ⊕ κ) T ▸ Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨x, rfl⟩ := hD
        cases x with
        | inl i =>
            rw [partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
            exact Ideal.mem_map_of_mem _
              (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)
        | inr j =>
            rw [partialDeriv_inr_algebraMap k ι κ S T hcoord j y]
            exact Submodule.zero_mem _
    | zero =>
        rw [zero_apply]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        rw [add_apply]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        rw [smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_left _ _ ha
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
    refine ⟨fun y hy => Ideal.mem_comap.mpr (le_derivIdeal k _ (Ideal.mem_map_of_mem _ hy)), ?_⟩
    intro D y hy
    exact Ideal.mem_comap.mpr (key1 D y hy)
  · rw [derivIdeal_le_iff]
    refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
    intro D' z hz
    refine derivation_apply_mem_of_mem_span D' (Ideal.map_mono (le_derivIdeal k J)) ?_ hz
    rintro g ⟨y, hy, rfl⟩
    exact key2 D' y hy

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
