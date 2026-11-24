module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Invariant.Profinite
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

open IsLocalRing

theorem exists_algEquiv_rootOfUnity_eq_pow (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (V ⧸ maximalIdeal V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra V Ω] [IsScalarTower V K Ω] :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ (x : Ω) (m : ℕ), (m : V) ∉ maximalIdeal V → x ^ m = 1 →
      φ x = x ^ Nat.card (V ⧸ maximalIdeal V) := by
  have : IsGalois K Ω := {}
  have hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace (integralClosure V Ω) := ⊥
  have : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral V k := by
      have h2 : IsIntegral V (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff ).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V (integralClosure V Ω) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact fun a b hab => hinj (congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure V Ω) (maximalIdeal V)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let : Field (integralClosure V Ω ⧸ Q) := Ideal.Quotient.field _
  let : Fintype (V ⧸ maximalIdeal V) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) := by
    have hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver _ _
    exact hi.isAlgebraic
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  have hu : Q.under V = maximalIdeal V := hQo.over.symm
  have hF : IsArithFrobAt V σ.1 Q := by
    intro x
    have h := DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rwa [← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]
  refine ⟨σ.1, fun x m hm hx => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))
  have hxi : IsIntegral V x := IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)
  have hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q := by
    intro h
    apply hm
    rwa [← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m)
    (Subtype.ext hx) hmQ
  rw [hu] at h
  exact congrArg Subtype.val h

theorem exists_frobenius_Kur (l : ℕ) [Fact l.Prime] :
    ∃ σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (Om l)
  rw [hcard] at hφ
  have hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l := by
    intro x m hm hx
    refine hφ x m (fun h => hm ?_) hx
    rwa [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
  have hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  refine ⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra
    (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩
  exact hφ' c m hlm (congrArg Subtype.val hc)

end GlobalTheory.MemLoc
