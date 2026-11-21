import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.DatumS
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldTopMaximalUnramified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassGroupCoprimeRepresentative
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.HostDatumExists

theorem exists_reps (K : Type) [Field K] [NumberField K] {ι : Type} [Finite ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = c ∧
      (∀ i, IsCoprime (I : Ideal (𝓞 K)) (Ideal.span {((n i : ℕ) : 𝓞 K)})) ∧
      ∀ 𝔭 ∈ S, ¬ (I : Ideal (𝓞 K)) ≤ 𝔭.asIdeal := by
  classical
  have := Fintype.ofFinite ι
  set m : Ideal (𝓞 K) := (∏ i, Ideal.span {((n i : ℕ) : 𝓞 K)}) * ∏ 𝔭 ∈ hS.toFinset, 𝔭.asIdeal with hm
  have hm0 : m ≠ ⊥ := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => 𝔭.ne_bot)
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn i
  obtain ⟨I, hI, hsup⟩ := GlobalTheory.exists_integral_ideal_in_class_coprime K m hm0 c
  refine ⟨I, hI, fun i => ?_, fun 𝔭 h𝔭 hle => 𝔭.isPrime.ne_top ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, ← top_le_iff, ← hsup]
    refine sup_le_sup_left (Ideal.le_of_dvd (Dvd.dvd.mul_right ?_ _)) _
    exact Finset.dvd_prod_of_mem (fun i => Ideal.span {((n i : ℕ) : 𝓞 K)}) (Finset.mem_univ i)
  · have h : m ≤ 𝔭.asIdeal :=
      Ideal.le_of_dvd (Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (hS.mem_toFinset.mpr h𝔭)) _)
    exact top_le_iff.mp (hsup ▸ sup_le hle h)

theorem le_of_integral {A B : Formalism.L2.Host.Fld} (h : ∀ x ∈ A, IsIntegral ℤ x → x ∈ B) : A ≤ B := by
  intro x hx
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  have h1 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Qb).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, hi⟩ := h1.exists_integral_multiple
  have h2 : a • x ∈ B := h _ (zsmul_mem hx a) hi
  have h3 : x = ((a : Qb))⁻¹ * (a • x) := by
    have : (a : Qb) ≠ 0 := by exact_mod_cast ha
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ this]
  rw [h3]
  exact mul_mem (inv_mem (intCast_mem B a)) h2

end GlobalTheory.HostDatumExists
