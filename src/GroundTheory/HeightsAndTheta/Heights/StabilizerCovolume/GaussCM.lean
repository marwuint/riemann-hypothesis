import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements.Gauss

open NumberField Polynomial
open scoped Matrix ComplexConjugate

abbrev Em : Type := CyclotomicField 4 ℚ

instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance cycl4 : IsCyclotomicExtension {4} ℚ Em := CyclotomicField.isCyclotomicExtension 4 ℚ

instance gaussian_isCyclotomic_four : IsCyclotomicExtension {2 ^ 2} ℚ Em := CyclotomicField.isCyclotomicExtension 4 ℚ

instance : IsCMField Em :=
  IsCyclotomicExtension.Rat.isCMField Em (S := {4}) ⟨4, Set.mem_singleton _, by norm_num⟩

def ζ : Em := IsCyclotomicExtension.zeta 4 ℚ Em

theorem hζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ Em

theorem ζ_sq : ζ ^ 2 = -1 := by
  have h4 : ζ ^ 4 = 1 := hζ.pow_eq_one
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
  have h : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = ζ ^ 4 - 1 := by ring
  rw [h4, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact eq_neg_of_add_eq_zero_left h

theorem exists_of_mem_adjoin {R : Type} [CommRing R] [Algebra R Em] {x : Em}
    (hx : x ∈ Algebra.adjoin R ({ζ} : Set Em)) :
    ∃ a b : R, x = algebraMap R Em a + algebraMap R Em b * ζ := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨0, 1, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact ⟨a + c, b + d, by simp only [map_add]; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    simp only [map_sub, map_add, map_mul]
    linear_combination (algebraMap R Em b * algebraMap R Em d) * ζ_sq

theorem exists_rat (x : Em) : ∃ a b : ℚ, x = (a : Em) + (b : Em) * ζ := by
  have hx : x ∈ Algebra.adjoin ℚ ({ζ} : Set Em) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    trivial
  obtain ⟨a, b, h⟩ := exists_of_mem_adjoin hx
  exact ⟨a, b, by rw [h, eq_ratCast, eq_ratCast]⟩

theorem exists_int {x : Em} (hx : IsIntegral ℤ x) : ∃ a b : ℤ, x = (a : Em) + (b : Em) * ζ := by
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p := 2) (k := 2) (ζ := ζ) (hcycl := gaussian_isCyclotomic_four) hζ
  obtain ⟨y, rfl⟩ := hcl.isIntegral_iff.1 hx
  obtain ⟨a, b, h⟩ := exists_of_mem_adjoin (R := ℤ) y.2
  refine ⟨a, b, Eq.trans ?_ (h.trans (by rw [eq_intCast, eq_intCast]))⟩
  rfl

abbrev cc : Em ≃ₐ[maximalRealSubfield Em] Em := IsCMField.complexConj Em

def φ₀ : Em →+* ℂ := Classical.choice inferInstance

theorem emb_ζ (σ : Em →+* ℂ) : σ ζ = Complex.I ∨ σ ζ = -Complex.I := by
  have hs : σ ζ ^ 2 = -1 := by rw [← map_pow, ζ_sq, map_neg, map_one]
  have h : (σ ζ - Complex.I) * (σ ζ + Complex.I) = σ ζ ^ 2 - Complex.I ^ 2 := by ring
  rw [hs, Complex.I_sq, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem ringHom_ext {σ σ' : Em →+* ℂ} (h : σ ζ = σ' ζ) : σ = σ' := by
  have : σ.toRatAlgHom = σ'.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  ext x
  exact congrArg (fun f : Em →ₐ[ℚ] ℂ => f x) this

theorem conj_emb_ζ (σ : Em →+* ℂ) : conj (σ ζ) = -σ ζ := by
  rcases emb_ζ σ with h | h <;> rw [h] <;> simp [Complex.conj_I]

theorem cc_ζ : cc ζ = -ζ := by
  apply φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg, conj_emb_ζ]

theorem cmType (σ : Em →+* ℂ) :
    (∃ τ : Unit, (fun _ => φ₀) τ = σ) ↔ ¬ ∃ τ : Unit, (fun _ => φ₀) τ = (starRingEnd ℂ).comp σ := by
  simp only [exists_const]
  constructor
  · rintro rfl h
    have h1 := congrArg (fun f : Em →+* ℂ => f ζ) h
    simp only [RingHom.coe_comp, Function.comp_apply, conj_emb_ζ] at h1
    have h0 : φ₀ ζ ≠ 0 := by rcases emb_ζ φ₀ with h | h <;> rw [h] <;> simp [Complex.I_ne_zero]
    exact h0 (by linear_combination h1 / 2)
  · intro h
    rcases emb_ζ σ with hs | hs <;> rcases emb_ζ φ₀ with hp | hp
    · exact ringHom_ext (hp.trans hs.symm)
    · exact absurd (ringHom_ext (by simp [hs, hp, Complex.conj_I])) h
    · exact absurd (ringHom_ext (by simp [hs, hp, Complex.conj_I])) h
    · exact ringHom_ext (hp.trans hs.symm)

theorem finrank_Em : Module.finrank ℚ Em = 2 := by
  rw [IsCyclotomicExtension.finrank Em (cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

theorem trace_ζ : Algebra.trace ℚ Em ζ = 0 := by
  have h := Algebra.trace_eq_of_algEquiv (cc.restrictScalars ℚ) ζ
  rw [AlgEquiv.restrictScalars_apply, cc_ζ, map_neg] at h
  linarith

theorem trace_rep (a b : ℚ) : Algebra.trace ℚ Em ((a : Em) + (b : Em) * ζ) = 2 * a := by
  have h1 : Algebra.trace ℚ Em (a : Em) = 2 * a := by
    rw [← eq_ratCast (algebraMap ℚ Em) a, Algebra.trace_algebraMap, finrank_Em, nsmul_eq_mul]
    norm_num
  have h2 : Algebra.trace ℚ Em ((b : Em) * ζ) = 0 := by
    rw [← eq_ratCast (algebraMap ℚ Em) b, ← Algebra.smul_def, map_smul, trace_ζ, smul_zero]
  rw [map_add, h1, h2, add_zero]

def gaussL : Submodule (𝓞 Em) (Fin 2 → Em) where
  carrier := {x | ∀ a, IsIntegral ℤ (x a)}
  add_mem' hx hy a := (hx a).add (hy a)
  zero_mem' _ := isIntegral_zero
  smul_mem' c x hx a := by
    show IsIntegral ℤ ((c • x) a)
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (hx a)

theorem single_mem (a : Fin 2) {v : Em} (hv : IsIntegral ℤ v) : Pi.single a v ∈ gaussL := by
  intro b
  by_cases h : b = a
  · subst h; simpa using hv
  · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero

theorem cc_isIntegral {v : Em} (hv : IsIntegral ℤ v) : IsIntegral ℤ (cc v) :=
  hv.map (cc : Em →+* Em).toIntAlgHom

end GroundTheory.Heights₂.Heights.NineStatements.Gauss
