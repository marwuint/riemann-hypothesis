import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGenerator

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine ⟨zpow_ne_zero n h0, ?_, ?_⟩
  · rcases n with m | m
    · simpa using pow_mem h1 m
    · simpa [zpow_negSucc] using pow_mem h2 (m + 1)
  · rcases n with m | m
    · simpa using pow_mem h2 m
    · simpa [zpow_negSucc] using pow_mem h1 (m + 1)

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨hs0, hs⟩ := hs
  obtain ⟨ht0, ht⟩ := ht
  have h1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht, hs]
    exact Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs, ht]
    exact Submodule.mem_span_singleton_self t
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp h2
  refine ⟨div_ne_zero hs0 ht0, ?_, ?_⟩
  · have e : s / t = (u : Ω) := by
      rw [← hu, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self ht0, mul_one]
    rw [e]
    exact u.2
  · have e : (s / t)⁻¹ = (w : Ω) := by
      rw [inv_div, ← hw, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self hs0, mul_one]
    rw [e]
    exact w.2

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  obtain ⟨ht0, ht⟩ := ht
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hs0 : s ≠ 0 := by
    intro h
    apply hu0
    rw [h, zero_div]
  refine ⟨hs0, ?_⟩
  have hunit : IsUnit (⟨s / t, hu1⟩ : regAt ξ p) :=
    ⟨⟨⟨s / t, hu1⟩, ⟨(s / t)⁻¹, hu2⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have hst : (⟨s / t, hu1⟩ : regAt ξ p) • t = s := by
    rw [Subring.smul_def, smul_eq_mul]
    exact div_mul_cancel₀ s ht0
  rw [ht, ← hst, Submodule.span_singleton_smul_eq hunit]

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  obtain ⟨ht0, htl⟩ := h
  have hg : ∃ g, Λ.IsGenAt p g := by
    by_contra hno
    push_neg at hno
    have hmem : t ∈ (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p := by
      rw [htl]
      exact Submodule.mem_span_singleton_self t
    have hbot : (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p = ⊥ := by
      unfold Lat.tens
      rw [Submodule.span_eq_bot]
      rintro x ⟨s, hs, -⟩
      exact absurd (hs ()) (hno (s ()))
    rw [hbot, Submodule.mem_bot] at hmem
    exact ht0 hmem
  obtain ⟨g, hg⟩ := hg
  have hg0 : g ≠ 0 := hg.1
  have hT : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p (g ^ σ) := by
    refine ⟨zpow_ne_zero σ hg0, ?_⟩
    unfold Lat.tens
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨s, hs, rfl⟩
      have hu := uZpow (gen_unit (hs ()) hg) σ
      have e : ∏ i : Unit, s i ^ σ = (⟨(s () / g) ^ σ, hu.2.1⟩ : regAt ξ p) • g ^ σ := by
        rw [Subring.smul_def, smul_eq_mul, Fintype.prod_unique]
        show s () ^ σ = (s () / g) ^ σ * g ^ σ
        rw [div_zpow, div_mul_cancel₀ _ (zpow_ne_zero σ hg0)]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.subset_span
      exact ⟨fun _ => g, fun _ => hg, by simp⟩
  have hu := gen_unit ⟨ht0, htl⟩ hT
  have hu2 := uZpow hu σ
  have heq : (t / g ^ σ) ^ σ = t ^ σ / g := by
    rw [div_zpow, ← zpow_mul, hσ, zpow_one]
  rw [heq] at hu2
  exact gen_of_unit hg hu2

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := h.1
  rw [Finset.prod_ne_zero_iff] at h0
  exact h0 k (Finset.mem_univ k)

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(map_ne_zero i).mpr h0, hreg a h1, ?_⟩
  rw [← map_inv₀]
  exact hreg _ h2

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

end LevelTowerAlt
