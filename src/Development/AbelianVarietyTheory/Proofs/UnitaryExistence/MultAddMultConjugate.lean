import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ReflexNormIndexIdeal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoeEqSpanDetOfIntVecLe

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatticeBetaCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise

section Index

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def detSpan (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) E := Submodule.span (𝓞 E) (detSet M)

omit [NumberField E] in
theorem detSet_eq (M : Submodule (𝓞 E) (Fin n → E)) :
    detSet M = {d | ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ M) ∧ d = (Matrix.of v).det} := by
  ext d
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [← Matrix.det_transpose (Matrix.of v)]
  rfl

theorem isUnit_detSpan (Λ : Lat E n) : IsUnit (detSpan Λ.L) := by
  obtain ⟨J, -, h0, -, hJ, -⟩ := GlobalTheory.TensorLat.exists_coe_eq_span_det (le_refl Λ.L) Λ.fg Λ.span_top
  rw [detSpan, detSet_eq, ← hJ]
  refine IsUnit.of_mul_eq_one ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ?_
  rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]

end Index

section Push

variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

theorem span_image_span (S : Set E) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 E) S : Set E)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : E) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 E) E →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

def coeI (E : Type) [Field E] : Ideal (𝓞 E) →* Submodule (𝓞 E) E where
  toFun := IsLocalization.coeSubmodule E
  map_one' := by rw [Ideal.one_eq_top, IsLocalization.coeSubmodule_top]
  map_mul' := IsLocalization.coeSubmodule_mul E

theorem smul_eq_coeI_mul (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) : 𝔞 • N = coeI E 𝔞 * N := by
  refine le_antisymm (Submodule.smul_le.2 fun a ha x hx => ?_) (Submodule.mul_le.2 ?_)
  · rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ⟨a, ha, rfl⟩ hx
  · rintro _ ⟨a, ha, rfl⟩ x hx
    exact (Algebra.smul_def a x) ▸ Submodule.smul_mem_smul ha hx

theorem span_image_ideal (𝔞 : Ideal (𝓞 E)) :
    Submodule.span (𝓞 F) (φ.comp (algebraMap (𝓞 E) E) '' (𝔞 : Set (𝓞 E))) =
      coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  change _ = IsLocalization.coeSubmodule F (Ideal.span _)
  rw [IsLocalization.coeSubmodule_span, Set.image_image]
  rfl

theorem extend_coeI (𝔞 : Ideal (𝓞 E)) :
    extend φ (coeI E 𝔞) = coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  rw [← span_image_ideal]
  change Submodule.span (𝓞 F) (φ '' (algebraMap (𝓞 E) E '' (𝔞 : Set (𝓞 E)))) = _
  rw [Set.image_image]
  rfl

theorem span_eq_coeI_iff [NumberField F] (β : F) (I : Ideal (𝓞 F)) :
    Submodule.span (𝓞 F) {β} = coeI F I ↔ ∃ b : 𝓞 F, (b : F) = β ∧ Ideal.span {b} = I := by
  constructor
  · intro h
    obtain ⟨b, -, rfl⟩ : β ∈ coeI F I := h ▸ Submodule.mem_span_singleton_self β
    refine ⟨b, rfl, IsFractionRing.coeSubmodule_injective (𝓞 F) F ?_⟩
    rw [IsLocalization.coeSubmodule_span_singleton]
    exact h
  · rintro ⟨b, rfl, rfl⟩
    exact (IsLocalization.coeSubmodule_span_singleton F b).symm

end Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem idealAt_eq (M : Submodule (𝓞 E) (Fin n → E)) (τ : E →+* ℂ) :
    idealAt c M τ = extend (embF c τ) (detSpan M) := (span_image_span _ _).symm

theorem coeI_reflexIdeal (𝔞 : Ideal (𝓞 E)) : coeI c.F (reflexIdeal Dw c 𝔞) =
    ∏ τ : E →+* ℂ, coeI c.F (𝔞.map (RingOfIntegers.mapRingHom (embF c τ))) ^ Dw.mult τ := by
  simp only [reflexIdeal, map_prod, map_pow]

variable {Dw c} in
theorem isBe_ne_zero {𝔞 : Ideal (𝓞 E)} (h0 : 𝔞 ≠ ⊥) {β : c.F} (h : IsBe Dw c 𝔞 β) : β ≠ 0 := by
  rintro rfl
  have := h.2 c.F.val.toRingHom
  rw [map_zero, norm_zero, zero_pow two_ne_zero] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h0)) this.symm

variable {Dw c} in

theorem isBe_unique {𝔞 : Ideal (𝓞 E)} (h0 : 𝔞 ≠ ⊥) {β β' : c.F} (h : IsBe Dw c 𝔞 β) (h' : IsBe Dw c 𝔞 β') :
    ∃ ζ : c.F, IsOfFinOrder ζ ∧ β' = ζ * β := by
  have hβ := isBe_ne_zero h0 h
  obtain ⟨⟨b, rfl, hb⟩, ha⟩ := h
  obtain ⟨⟨b', rfl, hb'⟩, ha'⟩ := h'
  obtain ⟨u, rfl⟩ : ∃ u, u * b = b' := Ideal.mem_span_singleton'.1 (by
    rw [hb, ← hb']; exact Ideal.mem_span_singleton_self _)
  refine ⟨u, isOfFinOrder_iff_pow_eq_one.2 ?_, rfl⟩
  obtain ⟨m, hm, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one c.F ℂ u.isIntegral_coe fun s => by
    have h1 := (ha' s).trans (ha s).symm
    have h2 : ‖s b‖ ≠ 0 := by simpa using hβ
    rw [pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero] at h1
    change ‖s ((u : c.F) * b)‖ = _ at h1
    rw [map_mul, norm_mul] at h1
    exact mul_right_cancel₀ h2 (h1.trans (one_mul _).symm)
  exact ⟨m, hm, h⟩

theorem mult_add_mult_conjugate (τ : E →+* ℂ) :
    Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have h2 : starRingEnd ℂ (τ (H.rt : E)) = -τ (H.rt : E) := by
    generalize τ (H.rt : E) = z at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at hre him
    have h0 : z.re = 0 := by
      by_contra h
      have : z.im = 0 := mul_left_cancel₀ h (by linarith)
      rw [this] at hre
      nlinarith
    apply Complex.ext <;> simp [h0]
  have h3 : H.rt0 ≠ -H.rt0 := fun h => by
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have := H.sqrt_neg_disc_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  simp only [Datum.mult, ComplexEmbedding.conjugate_coe_eq, h2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · rw [h, if_pos rfl, if_neg h3.symm]
  · rw [h, neg_neg, if_pos rfl, if_neg h3.symm, add_comm]

theorem norm_reflexNorm (γ : E) (s : c.F →+* ℂ) :
    ‖s (reflexNorm Dw c γ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ (Dw.p + Dw.q) := by
  have h1 : ∀ σ : E →+* ℂ, ‖s (embF c (ComplexEmbedding.conjugate σ) γ)‖ = ‖s (embF c σ γ)‖ := fun σ => by
    have e : embF c (ComplexEmbedding.conjugate σ) γ = embF c σ (IsCMField.complexConj E γ) :=
      Subtype.ext (IsCMField.complexEmbedding_complexConj E σ γ).symm
    have := IsCMField.complexEmbedding_complexConj E (s.comp (embF c σ)) γ
    rw [e]
    exact (congrArg norm this).trans (Complex.norm_conj _)
  have h2 : ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult σ =
      ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult (ComplexEmbedding.conjugate σ) := by
    rw [← Equiv.prod_comp (ComplexEmbedding.involutive_conjugate E).toPerm]
    simp only [Function.Involutive.coe_toPerm, h1]
  have h3 : |(Algebra.norm ℚ γ : ℝ)| = ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ := by
    have hb : Function.Bijective fun σ : E →+* ℂ => s.comp (embF c σ) :=
      Finite.injective_iff_bijective.1 fun σ τ h => RingHom.ext fun x =>
        congrArg Subtype.val (s.injective (DFunLike.congr_fun h x))
    rw [← norm_prod, Fintype.prod_bijective _ hb (fun σ => s (embF c σ γ)) (fun σ => σ γ) fun _ => rfl,
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ => σ γ) (fun σ : E →ₐ[ℚ] ℂ => σ γ) fun _ => rfl,
      ← Algebra.norm_eq_prod_embeddings]
    simp
  rw [reflexNorm, map_prod, norm_prod, h3, sq]
  simp only [map_pow, norm_pow]
  nth_rewrite 2 [h2]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun σ _ => by rw [← pow_add, mult_add_mult_conjugate]

theorem isBe_principal (γ : 𝓞 E) : IsBe Dw c (Ideal.span {γ}) (reflexNorm Dw c (γ : E)) := by
  refine ⟨⟨∏ σ : E →+* ℂ, RingOfIntegers.mapRingHom (embF c σ) γ ^ Dw.mult σ, ?_, ?_⟩, fun s => ?_⟩
  · change algebraMap (𝓞 c.F) c.F _ = _
    simp only [map_prod, map_pow]
    rfl
  · simp only [reflexIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
      Ideal.prod_span_singleton]
  · rw [norm_reflexNorm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    simp

theorem reflexIdeal_mul (𝔞 𝔟 : Ideal (𝓞 E)) :
    reflexIdeal Dw c (𝔞 * 𝔟) = reflexIdeal Dw c 𝔞 * reflexIdeal Dw c 𝔟 := by
  simp only [reflexIdeal, Ideal.map_mul, mul_pow, Finset.prod_mul_distrib]

theorem reflexIdeal_pow (𝔞 : Ideal (𝓞 E)) (h : ℕ) : reflexIdeal Dw c (𝔞 ^ h) = reflexIdeal Dw c 𝔞 ^ h := by
  simp only [reflexIdeal, Ideal.map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm h]

variable {Dw c}

theorem isBe_mul {𝔞 𝔟 : Ideal (𝓞 E)} {α β : c.F} (h : IsBe Dw c 𝔞 α) (h' : IsBe Dw c 𝔟 β) :
    IsBe Dw c (𝔞 * 𝔟) (α * β) := by
  obtain ⟨⟨a, rfl, ha⟩, h⟩ := h
  obtain ⟨⟨b, rfl, hb⟩, h'⟩ := h'
  refine ⟨⟨a * b, rfl, ?_⟩, fun s => ?_⟩
  · rw [reflexIdeal_mul, ← ha, ← hb, Ideal.span_singleton_mul_span_singleton]
  · rw [map_mul, norm_mul, mul_pow, h, h', map_mul, Nat.cast_mul, mul_pow]

theorem isBe_pow {𝔞 : Ideal (𝓞 E)} {α : c.F} (h : IsBe Dw c 𝔞 α) (k : ℕ) : IsBe Dw c (𝔞 ^ k) (α ^ k) := by
  induction k with
  | zero => simpa using isBe_top Dw c
  | succ k ih => rw [pow_succ, pow_succ]; exact isBe_mul ih h

theorem isBe_of_pow {𝔞 : Ideal (𝓞 E)} {ψ : c.F} {k : ℕ} (hk : 0 < k) (h : IsBe Dw c (𝔞 ^ k) (ψ ^ k)) :
    IsBe Dw c 𝔞 ψ := by
  obtain ⟨⟨b, hb, hI⟩, h⟩ := h
  have hψ : IsIntegral ℤ ψ := IsIntegral.of_pow hk (hb ▸ b.isIntegral_coe)
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : 𝓞 c.F, (b₀ : c.F) = ψ := ⟨⟨ψ, hψ⟩, rfl⟩
  refine ⟨⟨b₀, rfl, ?_⟩, fun s => ?_⟩
  · have e : b = b₀ ^ k := RingOfIntegers.ext hb
    rw [e, ← Ideal.span_singleton_pow, reflexIdeal_pow] at hI
    exact pow_left_injective hk.ne' hI
  · have := h s
    rw [map_pow, norm_pow, map_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm k, pow_mul,
      pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this

variable (Dw c)

end GlobalTheory.LatticeBetaCompare
