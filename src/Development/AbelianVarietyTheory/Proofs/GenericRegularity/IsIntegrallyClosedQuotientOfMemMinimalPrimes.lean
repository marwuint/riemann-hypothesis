module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GlobalTheory

theorem exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime {S : Type*} [CommRing S]
    {q : Ideal S} (hq : q ∈ minimalPrimes S) (m : Ideal S) [m.IsPrime] (hqm : q ≤ m)
    [IsDomain (Localization.AtPrime m)] {x : S} (hx : x ∈ q) :
    ∃ s : m.primeCompl, (s : S) * x = 0 := by
  have hPq : (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) ≤ q := by
    intro y hy
    have hy0 : algebraMap S (Localization.AtPrime m) y = 0 := hy
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ y).1 hy0
    have hsy : (s : S) * y ∈ q := by
      rw [hs]
      exact q.zero_mem
    have hsq : (s : S) ∉ q := fun h => s.2 (hqm h)
    exact (hq.1.1.mem_or_mem hsy).resolve_left hsq
  have hqP : q ≤ (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) :=
    hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hPq
  have hx0 : algebraMap S (Localization.AtPrime m) x = 0 := hqP hx
  exact (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 hx0

theorem isIntegrallyClosed_quotient_of_mem_minimalPrimes {S : Type*} [CommRing S]
    (hS : ∀ (m : Ideal S) [m.IsPrime],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m))
    {q : Ideal S} (hq : q ∈ minimalPrimes S) : IsIntegrallyClosed (S ⧸ q) := by
  have : q.IsPrime := hq.1.1
  refine IsIntegrallyClosed.of_localization_maximal (fun M _ _ => ?_)
  let m : Ideal S := M.comap (Ideal.Quotient.mk q)
  have : m.IsPrime := Ideal.comap_isPrime _ _
  have hqm : q ≤ m := Ideal.mk_ker.ge.trans (Ideal.comap_mono bot_le)
  obtain ⟨hdom, hic⟩ := hS m
  have hker : ∀ x ∈ q, algebraMap S (Localization.AtPrime m) x = 0 := fun x hx =>
    (IsLocalization.map_eq_zero_iff m.primeCompl _ x).2
      (exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime hq m hqm hx)
  let : Algebra (S ⧸ q) (Localization.AtPrime m) :=
    (Ideal.Quotient.lift q (algebraMap S (Localization.AtPrime m)) hker).toAlgebra
  have hmk : ∀ a : S, algebraMap (S ⧸ q) (Localization.AtPrime m) (Ideal.Quotient.mk q a) =
      algebraMap S (Localization.AtPrime m) a := fun a => Ideal.Quotient.lift_mk _ _ _
  have : IsLocalization M.primeCompl (Localization.AtPrime m) := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact hmk s ▸ IsLocalization.map_units (Localization.AtPrime m) (⟨s, hy⟩ : m.primeCompl)
    · intro z
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl z
      exact ⟨⟨Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q s, s.2⟩⟩, by simpa only [hmk] using h⟩
    · intro a b hab
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [hmk, hmk] at hab
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl _).1 hab
      refine ⟨⟨Ideal.Quotient.mk q c, c.2⟩, ?_⟩
      rw [← map_mul, ← map_mul, hc]
  exact hic.of_equiv (IsLocalization.algEquiv M.primeCompl (Localization.AtPrime M)
    (Localization.AtPrime m)).toRingEquiv.symm

theorem isIntegrallyClosed_quotient_minimalPrime_of_smooth :
    ∀ (F S : Type) [Field F] [CommRing S] [Algebra F S] [Algebra.Smooth F S] (q : Ideal S),
      q ∈ minimalPrimes S → IsIntegrallyClosed (S ⧸ q) := by
  intro F S _ _ _ _ q hq
  refine isIntegrallyClosed_quotient_of_mem_minimalPrimes (fun m _ => ?_) hq
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth F m (Localization.AtPrime m)

end GlobalTheory
