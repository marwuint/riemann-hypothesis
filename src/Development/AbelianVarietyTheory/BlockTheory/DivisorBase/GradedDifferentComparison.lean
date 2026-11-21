import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

set_option autoImplicit false

noncomputable section

open scoped NNReal NumberField Classical
open GlobalTheory.HTLat GlobalTheory.EigenSplit

namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison

section Valuations

variable {C : Type} [Field C]

def absDifferent (v : Valuation C ℝ≥0) {E : Type} [Field E] [NumberField E] (τ : E →+* C) : ℝ≥0 :=
  sSup {r | ∃ x ∈ differentIdeal ℤ (𝓞 E), v (τ x) = r}

set_option autoImplicit false in
open scoped NNReal NumberField Classical in
variable {C : Type} [Field C] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.exists_generator_different {v : Valuation C ℝ≥0} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    (τ : E →+* C) :
    ∃ δ : O, (differentIdeal ℤ (𝓞 E)).map (_root_.GlobalTheory.HTLat.embO hv τ) =
        Ideal.span {δ} ∧
      v (algebraMap O C δ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ≠ 0 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ ≤ 1 := by
  set f := _root_.GlobalTheory.HTLat.embO hv τ with hf
  have hemb : ∀ x : 𝓞 E, algebraMap O C (f x) = τ x :=
    _root_.GlobalTheory.HTLat.algebraMap_embO hv τ
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (differentIdeal ℤ (𝓞 E))
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hne
    rw [← hS]
    simp
  obtain ⟨g, hgS, hmax⟩ := Finset.exists_max_image S (fun g => v (τ g)) hSne
  have hgI : g ∈ differentIdeal ℤ (𝓞 E) := hS ▸ Submodule.subset_span hgS
  have hdvd : ∀ x ∈ differentIdeal ℤ (𝓞 E), f g ∣ f x := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      apply hv.dvd_of_le
      rw [hemb, hemb]
      exact hmax y hy
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact dvd_add ha hb
    | smul a b _ hb =>
      rw [smul_eq_mul, map_mul]
      exact dvd_mul_of_dvd_right hb _
  have hgreat : IsGreatest {r | ∃ x ∈ differentIdeal ℤ (𝓞 E), v (τ x) = r} (v (τ g)) := by
    refine ⟨⟨g, hgI, rfl⟩, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    rw [← hemb, ← hemb]
    exact hv.le_of_dvd (hdvd x hx)
  have habs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.absDifferent v τ = v (τ g) := hgreat.csSup_eq
  refine ⟨f g, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact hdvd x hx
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem f hgI
  · rw [habs, hemb]
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hx0' : v (τ x) ≠ 0 := by
      rw [Ne, map_eq_zero, map_eq_zero]
      exact_mod_cast hx0
    rw [habs]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hx0') (hgreat.2 ⟨x, hx, rfl⟩))
  · rw [habs, ← hemb]
    exact hv.map_le_one _

end Valuations

section PadicComplex

@[reducible] def algInt (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] 𝓞_ℂ_[p] := (padicIntHom p).toAlgebra

@[reducible] def algField (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] ℂ_[p] :=
  ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p)).toAlgebra

attribute [local instance] algInt algField

theorem tower (p : ℕ) [Fact p.Prime] :
    @IsScalarTower ℤ_[p] 𝓞_ℂ_[p] ℂ_[p] (algInt p).toSMul Algebra.toSMul (algField p).toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem fact_not_isUnit (p : ℕ) [Fact p.Prime] : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) :=
  ⟨PadicComplexHost.not_isUnit_p p⟩

attribute [local instance] tower fact_not_isUnit PadicComplexHost.isAdicComplete

def ramifiedOrLevel (E : Type) [Field E] [NumberField E] (level : ℕ) : Finset ℕ :=
  (2 * (NumberField.discr E).natAbs * level).primeFactors

def badPrimes (E : Type) [Field E] [NumberField E] (level : ℕ) (B : ℝ) : Finset ℕ :=
  (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ ramifiedOrLevel E level

instance factPrime {E : Type} [Field E] [NumberField E] {level : ℕ} {B : ℝ}
    (p : badPrimes E level B) : Fact (p : ℕ).Prime :=
  ⟨(Finset.mem_union.1 p.2).elim (fun h => (Finset.mem_filter.1 h).2) Nat.prime_of_mem_primeFactors⟩

end PadicComplex

end GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison
