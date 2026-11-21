import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem not_mem_flagStep {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (i : Fin r) :
    b i ∉ flagStep Ω b i := by
  exact hb.notMem_span_image (by simp)

theorem gr_isGenAt {r : ℕ} (L : Lat ξ E) (b b₀ : Fin r → E) (p : Cpt ξ) (hL : L.IsFrameAt b p)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) (c : Ω)
    (hc : b i - c • b₀ i ∈ flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨hb, hLp⟩ := hL
  have hbi : b i ∉ flagStep Ω b i := not_mem_flagStep b hb i
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hbi
    rw [hF]
    simpa using hc
  refine ⟨hc0, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨e, he, het⟩
    rw [hLp] at he
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).mp he
    have het' : ∑ k, (d k : Ω) • b k - t • b₀ i ∈ flagStep Ω b₀ i := het
    set S : Submodule Ω E := Submodule.span Ω (b '' {k | k ≠ i}) with hS
    have hFS : flagStep Ω b₀ i ≤ S := by
      rw [← hF]
      refine Submodule.span_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨k, fun hki => ?_, rfl⟩
      subst hki
      exact lt_irrefl (k : ℕ) hk
    have h1 : c • (∑ k, (d k : Ω) • b k - t • b₀ i) ∈ S := S.smul_mem c (hFS het')
    have h2 : c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k ∈ S :=
      S.smul_mem c (Submodule.sum_mem _ fun k hk =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, Finset.ne_of_mem_erase hk, rfl⟩))
    have h3 : t • (b i - c • b₀ i) ∈ S := S.smul_mem t (hFS hc)
    have heq : (c * (d i : Ω) - t) • b i =
        c • (∑ k, (d k : Ω) • b k - t • b₀ i) - c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k -
          t • (b i - c • b₀ i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      module
    have key : (c * (d i : Ω) - t) • b i ∈ S := by
      rw [heq]
      exact S.sub_mem (S.sub_mem h1 h2) h3
    have hzero : c * (d i : Ω) - t = 0 := by
      by_contra hne
      apply hb.notMem_span_image (s := {k | k ≠ i}) (x := i) (by simp)
      have := S.smul_mem (c * (d i : Ω) - t)⁻¹ key
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    refine Submodule.mem_span_singleton.mpr ⟨d i, ?_⟩
    show (d i : Ω) * c = t
    rw [mul_comm]
    exact sub_eq_zero.mp hzero
  · refine Submodule.span_le.mpr ?_
    rintro _ rfl
    refine Submodule.subset_span ⟨b i, ?_, hc⟩
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem zpow_ratio (Λ : Lat ξ Ω) (p : Cpt ξ) (s t : Ω) (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) (n : ℤ) :
    (t / s) ^ n ∈ regAt ξ p := by
  obtain ⟨hs0, hsp⟩ := hs
  obtain ⟨ht0, htp⟩ := ht
  have h1 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hsp, htp]
    exact Submodule.mem_span_singleton_self t
  have h2 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← htp, hsp]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp h2
  have hts : t / s = a := by
    rw [div_eq_iff hs0]
    exact ha.symm
  have hst : s / t = a' := by
    rw [div_eq_iff ht0]
    exact ha'.symm
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hts]
    exact pow_mem a.2 m
  · rw [zpow_negSucc, ← inv_pow, inv_div, hst]
    exact pow_mem a'.2 _

theorem tens_isGenAt {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨s', hs', rfl⟩
    have hr : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_ratio (Λ i) p (s i) (s' i) (hs i) (hs' i) (a i)
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hr⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨s, hs, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.FlagModel
