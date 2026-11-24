module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.v00 :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)) [U.Normal], IsOpen (U : Set (G F Ω)) → ∀ (g : G F Ω) (Sg : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), M ≠ 0 → ∃ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (p : ℕ) (σ : G F Ω), w ∉ Sg ∧ p.Prime ∧ ¬ p ∣ M ∧ ¬ (p : ℤ) ∣ discr F ∧ ((p : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ normV w = p ∧ locDeg w = 1 ∧ IsPlaceOver A w ∧ Ine (F := F) A ≤ U ∧ Formalism.ConjugateSelfDual.IsFrob (F := F) A p σ ∧ σ⁻¹ * g ∈ U := by
  intro F Ω _ _ _ _ _ _ U hU hUo g Sg M hM
  classical
  set N : ℕ := M * (discr F).natAbs with hNdef
  have hN0 : N ≠ 0 := Nat.mul_ne_zero hM (Int.natAbs_ne_zero.mpr (discr_ne_zero F))
  have hI : (Ideal.span {(N : 𝓞 F)} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hI
  obtain ⟨v, hvA, hinert, hram, B, hB, hBU, σ, hσ, hσg⟩ :=
    GlobalTheory.Published.cheb_holds F Ω U hUo hU g (Sg ∪ hfin.toFinset)
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hp : (normV v).Prime := by
    rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hinert
  have hpv : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hnorm]; exact Ideal.absNorm_mem _
  have hNv : (N : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hvA
    apply Finset.mem_union_right
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_le,
      Set.singleton_subset_iff]
    exact h
  have hdvd : ∀ k : ℕ, normV v ∣ k → (k : 𝓞 F) ∈ v.asIdeal := by
    rintro k ⟨c, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpv
  refine ⟨v, B, normV v, σ, fun h => hvA (Finset.mem_union_left _ h), hp, ?_, ?_, hpv, rfl,
    ?_, hB, hBU, hσ, ?_⟩
  · intro h
    exact hNv (hdvd N (dvd_mul_of_dvd_left h _))
  · intro h
    apply hNv
    apply hdvd
    apply dvd_mul_of_dvd_right
    exact Int.natCast_dvd.mp h
  · simp [locDeg, hram, hinert]
  · have h1 : g * σ⁻¹ ∈ U := by
      have := U.inv_mem hσg
      simpa using this
    simpa [mul_assoc] using hU.conj_mem _ h1 σ⁻¹
