module

public import ReciprocityTheory.Hypotheses.GalCohDefs
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.sum_local_degree_above_l_le_finrank :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∑ v ∈ S, if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) ≤ Module.finrank ℚ F := by
  intro F _ _ l hl S
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hpdef
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.mp hl.out)
  have hpb : p ≠ ⊥ := by
    rwa [hpdef, Ne, Ideal.span_singleton_eq_bot]
  haveI hpm : p.IsMaximal := hpp.isMaximal hpb
  have key := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
  rw [NumberField.RingOfIntegers.rank] at key
  rw [← key, ← Finset.sum_filter]
  set g : Ideal (𝓞 F) → ℕ := fun I => I.ramificationIdx ℤ * I.inertiaDeg ℤ with hg
  have h1 : ∑ v ∈ S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal), locDeg v
      = ∑ I ∈ (S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)).image (fun v => v.asIdeal), g I := by
    rw [Finset.sum_image]
    · rfl
    · exact fun a _ b _ hab => HeightOneSpectrum.ext hab
  have h2 : ∑ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ
      = ∑ I ∈ (Finset.univ : Finset (p.primesOver (𝓞 F))).image Subtype.val, g I := by
    rw [Finset.sum_image]
    exact fun a _ b _ hab => Subtype.ext hab
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    simp only [Finset.mem_image, Finset.mem_filter] at hI
    obtain ⟨v, ⟨_, hv⟩, rfl⟩ := hI
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    have hle : p ≤ Ideal.under ℤ v.asIdeal := by
      rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under, Ideal.mem_comap] using hv
    have hne : Ideal.under ℤ v.asIdeal ≠ ⊤ := (Ideal.IsPrime.under ℤ v.asIdeal).ne_top
    have heq : p = Ideal.under ℤ v.asIdeal := hpm.eq_of_le hne hle
    exact ⟨⟨v.asIdeal, ⟨v.isPrime, ⟨heq⟩⟩⟩, rfl⟩
  · exact fun _ _ _ => Nat.zero_le _
