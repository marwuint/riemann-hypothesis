import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsContinuousCircleCharExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear

noncomputable section

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.CharFin
open scoped TensorProduct nonZeroDivisors

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def diag : E →+* RA F E :=
  (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom

omit [NumberField E] in
theorem diag_apply (a : E) : diag F E a = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a := rfl

def diagInt : 𝓞 E →+* hatRing F E :=
  ((diag F E).comp (algebraMap (𝓞 E) E)).codRestrict _ fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩

theorem exists_denom (z : RA F E) : ∃ N : ℕ, 0 < N ∧ (N : RA F E) * z ∈ hatRing F E := by
  obtain ⟨x, h, hh, rfl⟩ := GlobalTheory.AdIdem.exists_eq_one_tmul_add F E z
  obtain ⟨N, hN, hx⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E x
  refine ⟨N, hN, ?_⟩
  rw [mul_add]
  refine add_mem ?_ (mul_mem (natCast_mem _ N) hh)
  have := one_tmul_mem_adelicCompletionOfElementSet F hx
  rw [← diag_apply, map_mul, map_natCast] at this
  exact this

omit [NumberField E] in
theorem isUnit_diag {a : E} (ha : a ≠ 0) : IsUnit (diag F E a) := (IsUnit.mk0 a ha).map _

theorem isUnit_nat {N : ℕ} (hN : 0 < N) : IsUnit (N : RA F E) := by
  have := isUnit_diag F E (a := (N : E)) (by exact_mod_cast hN.ne')
  rwa [map_natCast] at this

theorem pow_classNumber_integral (x : hatRing F E) (hx : IsUnit (x : RA F E)) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ ∃ s t : hatRing F E, x ^ classNumber E = diagInt F E b * s ∧ s * t = 1 := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨M, hM, hMu⟩ := exists_denom F E (u⁻¹ : (RA F E)ˣ)
  let I : Ideal (𝓞 E) := (Ideal.span {x}).comap (diagInt F E)
  have hMx : (M : hatRing F E) ∈ Ideal.span {x} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨_, hMu⟩, Subtype.ext ?_⟩
    simp only [← hu, Subring.coe_natCast, Subring.coe_mul]
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hMI : (M : 𝓞 E) ∈ I := by
    rw [Ideal.mem_comap, map_natCast]; exact hMx
  have hI : I.map (diagInt F E) = Ideal.span {x} := by
    refine le_antisymm Ideal.map_comap_le ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    obtain ⟨a, w, hw, e⟩ := exists_int_add_nsmul F E M hM x x.2
    have e' : x = diagInt F E a + (M : hatRing F E) * ⟨w, hw⟩ := by
      apply Subtype.ext
      rw [e, nsmul_eq_mul]; simp; rfl
    have ha : a ∈ I := by
      rw [Ideal.mem_comap, ← sub_eq_iff_eq_add.2 e']
      exact sub_mem (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hMx)
    have hM' := Ideal.mem_map_of_mem (diagInt F E) hMI
    rw [map_natCast] at hM'
    rw [SetLike.mem_coe, e']
    exact add_mem (Ideal.mem_map_of_mem _ ha) (Ideal.mul_mem_right _ _ hM')
  have hI0 : I ∈ (Ideal (𝓞 E))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    rw [h] at hMI
    exact (Nat.cast_ne_zero.2 hM.ne') (Ideal.mem_bot.1 hMI)
  have hp : (I ^ classNumber E).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI0 _)]
    have : (⟨I ^ classNumber E, pow_mem hI0 _⟩ : (Ideal (𝓞 E))⁰) = ⟨I, hI0⟩ ^ classNumber E := rfl
    rw [this, map_pow]
    exact pow_card_eq_one
  obtain ⟨b, hb⟩ := hp
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact mem_nonZeroDivisors_iff_ne_zero.1 (pow_mem hI0 (classNumber E)) (by rw [hb]; simp)
  have h3 : Ideal.span {x ^ classNumber E} = Ideal.span {diagInt F E b} := by
    rw [← Ideal.span_singleton_pow, ← hI, ← Ideal.map_pow, hb, Ideal.submodule_span_eq, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 (h3 ▸ Ideal.mem_span_singleton_self (x ^ classNumber E))
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 (h3.symm ▸ Ideal.mem_span_singleton_self (diagInt F E b))
  refine ⟨b, hb0, s, t, hs, Subtype.ext ?_⟩
  have hx' : IsUnit ((x ^ classNumber E : hatRing F E) : RA F E) := by
    rw [SubmonoidClass.coe_pow, ← hu]; exact u.isUnit.pow _
  apply hx'.mul_left_cancel
  have : x ^ classNumber E * (s * t) = x ^ classNumber E * 1 := by
    linear_combination (-s) * ht - hs
  exact congrArg Subtype.val this

theorem pow_classNumber (x : (RA F E)ˣ) : ∃ b : E, b ≠ 0 ∧ ∃ s t : hatRing F E,
    (x : RA F E) ^ classNumber E = diag F E b * s ∧ s * t = 1 := by
  obtain ⟨N, hN, hx⟩ := exists_denom F E x
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber_integral F E ⟨_, hx⟩ ((isUnit_nat F E hN).mul x.isUnit)
  have hN' : (N : E) ^ classNumber E ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  refine ⟨(b : E) / (N : E) ^ classNumber E, div_ne_zero (by simpa using hb) hN', s, t, ?_, hst⟩
  apply (isUnit_diag F E hN').mul_left_cancel
  rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hN', map_pow, map_natCast, ← mul_pow]
  exact congrArg Subtype.val e

variable {F E} (c : E ≃ₐ[F] E)

abbrev bar : RA F E →ₐ[F] RA F E := sg (FiniteAdeleRing (𝓞 F) F) c

omit [NumberField E] in
theorem bar_tmul (a : FiniteAdeleRing (𝓞 F) F) (y : E) : bar c (a ⊗ₜ[F] y) = a ⊗ₜ[F] c y := rfl

omit [NumberField E] in
theorem bar_bar (hc : ∀ y, c (c y) = y) (z : RA F E) : bar c (bar c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [bar_tmul, bar_tmul, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [NumberField E] in
theorem bar_mem {z : RA F E} (hz : z ∈ hatRing F E) : bar c z ∈ hatRing F E := by
  refine galoisAut_mem_adelicCompletionOfElementSet F c ?_ hz
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨_, (RingOfIntegers.isIntegral_coe x).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩

def ratOne : Subgroup (RA F E)ˣ where
  carrier := {x | (∃ a : E, (x : RA F E) = diag F E a) ∧ (x : RA F E) * bar c x = 1}
  one_mem' := ⟨⟨1, by simp⟩, by simp⟩
  mul_mem' := by
    rintro x y ⟨⟨a, ha⟩, hx⟩ ⟨⟨b, hb⟩, hy⟩
    refine ⟨⟨a * b, by rw [Units.val_mul, ha, hb, map_mul]⟩, ?_⟩
    rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, mul_one]
  inv_mem' := by
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h : ((x⁻¹ : (RA F E)ˣ) : RA F E) = bar c x := Units.inv_eq_of_mul_eq_one_right hx
    refine ⟨⟨c a, by rw [h, ha]; rfl⟩, ?_⟩
    nth_rewrite 1 [h]
    rw [← map_mul, Units.mul_inv, map_one]

def congOne (N : ℕ) : Subgroup (RA F E)ˣ where
  carrier := {x | (∃ w ∈ hatRing F E, (x : RA F E) - 1 = N * w) ∧ (x : RA F E) * bar c x = 1}
  one_mem' := ⟨⟨0, zero_mem _, by simp⟩, by simp⟩
  mul_mem' := by
    rintro x y ⟨⟨a, ha, ea⟩, hx⟩ ⟨⟨b, hb, eb⟩, hy⟩
    refine ⟨⟨a + b + N * (a * b), add_mem (add_mem ha hb) (mul_mem (natCast_mem _ N) (mul_mem ha hb)), ?_⟩, ?_⟩
    · rw [Units.val_mul]
      linear_combination (y : RA F E) * ea + (1 + N * a) * eb
    · rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, mul_one]
  inv_mem' := by
    rintro x ⟨⟨a, ha, ea⟩, hx⟩
    have h : ((x⁻¹ : (RA F E)ˣ) : RA F E) = bar c x := Units.inv_eq_of_mul_eq_one_right hx
    refine ⟨⟨bar c a, bar_mem c ha, ?_⟩, ?_⟩
    · have := congrArg (bar c) ea
      rwa [map_sub, map_one, map_mul, map_natCast, ← h] at this
    · nth_rewrite 1 [h]
      rw [← map_mul, Units.mul_inv, map_one]

theorem exists_exponent (hc : ∀ y, c (c y) = y) (N : ℕ) (hN : 0 < N) : ∃ m : ℕ, 0 < m ∧
    ∀ x : (RA F E)ˣ, (x : RA F E) * bar c x = 1 → x ^ m ∈ ratOne c ⊔ congOne c N := by
  have := finite_quotient_hatRing F E N hN
  let k := Nat.card (hatRing F E ⧸ Ideal.span {(N : hatRing F E)})ˣ
  refine ⟨classNumber E * 2 * k, Nat.mul_pos (Nat.mul_pos (classNumber_pos E) two_pos) Nat.card_pos,
    fun x hx => ?_⟩
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber F E x
  have hst' : (s : RA F E) * t = 1 := congrArg Subtype.val hst
  have hbst : bar c s * bar c t = 1 := by rw [← map_mul, hst', map_one]
  have hcb : c b ≠ 0 := by simpa using hb
  have hq : b / c b ≠ 0 := div_ne_zero hb hcb
  let r : (RA F E)ˣ := (isUnit_diag F E hq).unit
  have hr : r ∈ ratOne c := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    change diag F E (b / c b) * diag F E (c (b / c b)) = 1
    rw [← map_mul, map_div₀, hc, div_mul_div_comm, mul_comm b, div_self (mul_ne_zero hcb hb), map_one]
  let v : (hatRing F E)ˣ := Units.mkOfMulEqOne (s * ⟨_, bar_mem c t.2⟩) (t * ⟨_, bar_mem c s.2⟩)
    (Subtype.ext (by
      change (s : RA F E) * bar c t * (t * bar c s) = 1
      linear_combination (bar c s * bar c t) * hst' + hbst))
  let u : (RA F E)ˣ := Units.map (hatRing F E).subtype.toMonoidHom v
  have hu : (u : RA F E) = s * bar c t := rfl
  have hun : (u : RA F E) * bar c u = 1 := by
    rw [hu, map_mul, bar_bar c hc]
    linear_combination (bar c s * bar c t) * hst' + hbst
  have hx2 : x ^ (classNumber E * 2) = r * u := by
    apply Units.ext
    have h1 : (x : RA F E) ^ classNumber E * bar c ((x : RA F E) ^ classNumber E) = 1 := by
      rw [map_pow, ← mul_pow, hx, one_pow]
    have h2 : diag F E (b / c b) * diag F E (c b) = diag F E b := by
      rw [← map_mul, div_mul_cancel₀ _ hcb]
    have h3 : bar c (diag F E b) = diag F E (c b) := rfl
    rw [e, map_mul, h3] at h1
    rw [Units.val_pow_eq_pow_val, pow_mul, e, Units.val_mul, hu]
    change _ = diag F E (b / c b) * _
    linear_combination (diag F E (b / c b) * s * bar c t) * h1 - (diag F E b * s * s) * h2
      - (diag F E (b / c b) * diag F E (c b) * diag F E b * s * s) * hbst
  have huk : u ^ k ∈ congOne c N := by
    refine ⟨?_, by rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]⟩
    have h1 : (Units.map (Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)})).toMonoidHom v) ^ k = 1 :=
      pow_card_eq_one'
    have h2 : Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)}) ((v : hatRing F E) ^ k) =
        Ideal.Quotient.mk _ 1 := by
      rw [map_pow, map_one]
      exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val h1)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h2)
    refine ⟨w, w.2, ?_⟩
    have := congrArg (hatRing F E).subtype hw
    rwa [map_sub, map_one, map_mul, map_natCast, map_pow] at this
  rw [pow_mul, hx2, mul_pow]
  exact Subgroup.mul_mem_sup (pow_mem hr k) huk

theorem mem_of_pow_eq_one {K : IntermediateField ℚ ℂ} {m : ℕ} (hm : 0 < m)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta m ∈ K) {z : ℂ} (hz : z ^ m = 1) : z ∈ K := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp m hm.ne').eq_pow_of_pow_eq_one hz
  exact pow_mem h i

end GlobalTheory.NormOneChar

namespace GlobalTheory.NormOneChar

end GlobalTheory.NormOneChar
