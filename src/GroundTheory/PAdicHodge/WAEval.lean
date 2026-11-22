import Mathlib
import GroundTheory.PAdicHodge.WACommon
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.ACrisBdR
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAEval

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace IsPerfectoidField Laurent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔍" => RingHom.ker (fontaineThetaInvertP (normInteger ℂ_[p]) p)
local notation "θ" => fontaineTheta (normInteger ℂ_[p]) p

theorem norm_natCast_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem inv_p_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt)

variable (p) in

def varpi : Cb p := algebraMap (Ob p) (Cb p) (pFlat p)

theorem norm_varpi : ‖varpi p‖ = (p : ℝ)⁻¹ := by
  rw [varpi, norm_algebraMap_preTilt, preTilt_norm_def, untilt_pFlat]
  push_cast
  exact norm_natCast_p

theorem varpi_ne_zero : varpi p ≠ 0 := by
  intro h
  have := norm_varpi (p := p)
  rw [h, norm_zero] at this
  exact inv_p_pos.ne this

theorem norm_varpi_lt_one : ‖varpi p‖ < 1 := by
  rw [norm_varpi]; exact inv_p_lt_one

variable (p) in

def xi : (𝓣).int := (𝓣).ptElt (norm_varpi_lt_one (p := p)).le

theorem isPrimOne_xi : (𝓣).IsPrimOne (xi p) := (𝓣).isPrimOne_ptElt varpi_ne_zero norm_varpi_lt_one

theorem ptRad_xi : (𝓣).ptRad (xi p) = (p : ℝ)⁻¹ := by
  rw [ptRad, coeff_zero, xi, coe_ptElt, map_sub, red_π, red_teich, zero_sub, norm_neg, norm_varpi]

variable (p) in

def xiA : AInf ℂ_[p] p := (p : AInf ℂ_[p] p) - teichmuller p (pFlat p)

theorem ker_theta_eq_span_xiA : RingHom.ker θ = Ideal.span {xiA p} :=
  IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller untilt_pFlat

theorem incl_xiA : incl ℂ_[p] p (xiA p) = ((xi p : (𝓣).int) : WC p) := by
  rw [xiA, map_sub, map_natCast, incl_teichmuller, xi, coe_ptElt, teich_eq, teichLift_π]
  rfl

theorem ker_eq_span_xiA : 𝔍 = Ideal.span {algebraMap (AInf ℂ_[p] p) 𝔸 (xiA p)} :=
  ker_fontaineThetaInvertP ker_theta_eq_span_xiA

theorem ker_pow_eq_span (m : ℕ) : 𝔍 ^ m = Ideal.span {algebraMap (AInf ℂ_[p] p) 𝔸 (xiA p) ^ m} := by
  rw [ker_eq_span_xiA, Ideal.span_singleton_pow]

theorem convAll_pow {b : (𝓣).B} (hb : (𝓣).ConvAll b) (k : ℕ) : (𝓣).ConvAll (b ^ k) := by
  induction k with
  | zero => rw [pow_zero]; simpa using (TeichLift.convAll_π_pow (T := 𝓣) 0)
  | succ k ih => rw [pow_succ]; exact ih.mul hb

theorem toB_eq_mul (a : 𝔸) : ∃ (N : ℕ) (y : AInf ℂ_[p] p), toB ℂ_[p] p a =
    algebraMap (WC p) (𝓣).B (incl ℂ_[p] p y) * IsLocalization.Away.invSelf (𝓣).π ^ N := by
  obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj (p : AInf ℂ_[p] p) a
  refine ⟨N, y, ?_⟩
  have h := congrArg (toB ℂ_[p] p) hy
  rw [map_mul, map_pow, toB_algebraMap, toB_algebraMap] at h
  have e : algebraMap (WC p) (𝓣).B (incl ℂ_[p] p (p : AInf ℂ_[p] p)) =
      algebraMap (WC p) (𝓣).B (𝓣).π := by
    rw [map_natCast (incl ℂ_[p] p)]; rfl
  rw [← h, mul_assoc, ← mul_pow, e, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem convAll_toB (a : 𝔸) : (𝓣).ConvAll (toB ℂ_[p] p a) := by
  obtain ⟨N, y, hy⟩ := toB_eq_mul a
  rw [hy]
  exact (convAll_algebraMap_of_mem_int (incl_mem_int y)).mul (convAll_pow convAll_invSelf N)

variable (p) in

def awayToEcon (ρ : Set.Ioo (0 : ℝ) 1) : 𝔸 →+* (𝓣).Econ ρ :=
  (toB ℂ_[p] p).codRestrict ((𝓣).Econ ρ) fun a => convAll_toB a ρ ρ.2.1 ρ.2.2

variable (p) in

def awayToExt (ρ : Set.Ioo (0 : ℝ) 1) : 𝔸 →+* (𝓣).RobbaExt ρ :=
  Completion.coeRingHom.comp (awayToEcon p ρ)

theorem awayToExt_apply (ρ : Set.Ioo (0 : ℝ) 1) (a : 𝔸) :
    awayToExt p ρ a = ((⟨toB ℂ_[p] p a, convAll_toB a ρ ρ.2.1 ρ.2.2⟩ : (𝓣).Econ ρ) :
      (𝓣).RobbaExt ρ) := rfl

theorem res_awayToExt {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (a : 𝔸) :
    (𝓣).res h (awayToExt p ρ0 a) = awayToExt p ρ1 a := by
  rw [awayToExt_apply, res_coe]
  rfl

theorem awayToExt_xiA (ρ : Set.Ioo (0 : ℝ) 1) :
    awayToExt p ρ (algebraMap (AInf ℂ_[p] p) 𝔸 (xiA p)) = (𝓣).ξExt (xi p) ρ := by
  rw [awayToExt_apply, ξExt]
  congr 2
  rw [toB_algebraMap, incl_xiA]

theorem res_ξExt {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    (𝓣).res h ((𝓣).ξExt (xi p) ρ0) = (𝓣).ξExt (xi p) ρ1 := by
  rw [← awayToExt_xiA, ← awayToExt_xiA, res_awayToExt]

theorem ξExt_ne_zero (ρ : Set.Ioo (0 : ℝ) 1) : (𝓣).ξExt (xi p) ρ ≠ 0 := by
  intro h
  have h1 := (𝓣).ptRad_le_extNorm_ξExt (ξ := xi p) (topRad ρ)
  rw [h, extNorm_zero, ptRad_xi] at h1
  exact absurd h1 (not_le.2 inv_p_pos)

theorem toUntiltField_injective : Function.Injective ((𝓣).toUntiltField (isPrimOne_xi (p := p))) :=
  fun _ _ h => (𝓣).algebraMap_untiltFrac_injective isPrimOne_xi
    ((WithAbs.equiv ((𝓣).untiltAbs isPrimOne_xi)).symm.injective h)

variable (p) in

def thetaXi : 𝔸 →+* (𝓣).UntiltField (isPrimOne_xi (p := p)) :=
  ((𝓣).ptEvalEcon isPrimOne_xi).comp (awayToEcon p ((𝓣).ptRadIoo isPrimOne_xi))

theorem thetaXi_apply (a : 𝔸) : thetaXi p a = (𝓣).ptEvalB isPrimOne_xi (toB ℂ_[p] p a) := rfl

theorem ptEval_awayToExt {ρ : Set.Ioo (0 : ℝ) 1} (hr : (𝓣).ptRad (xi p) ≤ ρ) (a : 𝔸) :
    (𝓣).ptEval isPrimOne_xi hr (awayToExt p ρ a) = thetaXi p a := by
  rw [awayToExt_apply, ptEval_coe]
  rfl

theorem thetaXi_algebraMap (y : AInf ℂ_[p] p) :
    thetaXi p (algebraMap _ 𝔸 y) = (𝓣).toUntiltField isPrimOne_xi
      ((𝓣).toUntilt (xi p) ⟨incl ℂ_[p] p y, incl_mem_int y⟩) := by
  rw [thetaXi_apply, toB_algebraMap, ptEvalB_algebraMap, ptE_int]

theorem thetaXi_algebraMap_p :
    thetaXi p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p)) = (𝓣).ptPi isPrimOne_xi := by
  rw [thetaXi_algebraMap, ptPi]
  congr 2
  exact Subtype.ext (map_natCast (incl ℂ_[p] p) p)

theorem thetaXi_algebraMap_eq_zero_iff (y : AInf ℂ_[p] p) :
    thetaXi p (algebraMap _ 𝔸 y) = 0 ↔ y ∈ Ideal.span {xiA p} := by
  rw [thetaXi_algebraMap, map_eq_zero_iff _ toUntiltField_injective, toUntilt_eq_zero_iff,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨B, ⟨c, rfl⟩, hB⟩
    refine ⟨c, incl_injective ?_⟩
    rw [map_mul, incl_xiA, mul_comm]
    exact hB.symm
  · rintro ⟨c, rfl⟩
    refine ⟨incl ℂ_[p] p c, ⟨c, rfl⟩, ?_⟩
    show incl ℂ_[p] p (c * xiA p) = _
    rw [map_mul, incl_xiA, mul_comm]

theorem natCast_p_normInteger_ne_zero : ((p : normInteger ℂ_[p]) : normInteger ℂ_[p]) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : normInteger ℂ_[p] => ‖(x : ℂ_[p])‖) h
  simp only [ZeroMemClass.coe_zero, norm_zero] at h'
  push_cast at h'
  rw [norm_natCast_p] at h'
  exact inv_p_pos.ne' h'

theorem fontaineThetaInvertP_algebraMap_eq_zero_iff (y : AInf ℂ_[p] p) :
    fontaineThetaInvertP (normInteger ℂ_[p]) p (algebraMap _ 𝔸 y) = 0 ↔ θ y = 0 := by
  rw [fontaineThetaInvertP_algebraMap]
  exact map_eq_zero_iff _ (IsLocalization.injective (M := Submonoid.powers (p : normInteger ℂ_[p]))
      (Localization.Away (p : normInteger ℂ_[p]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors natCast_p_normInteger_ne_zero))

theorem thetaXi_eq_zero_iff (a : 𝔸) : thetaXi p a = 0 ↔ a ∈ 𝔍 := by
  obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj (p : AInf ℂ_[p] p) a
  rw [RingHom.mem_ker]
  have hP : thetaXi p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p)) ≠ 0 := by
    rw [thetaXi_algebraMap_p]; exact (𝓣).ptPi_ne_zero isPrimOne_xi
  have h1 : thetaXi p a = 0 ↔ thetaXi p (algebraMap _ 𝔸 y) = 0 := by
    rw [← hy, map_mul, map_pow, mul_eq_zero, or_iff_left (pow_ne_zero N hP)]
  have hU : IsUnit (fontaineThetaInvertP (normInteger ℂ_[p]) p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p))) := by
    rw [fontaineThetaInvertP_algebraMap, map_natCast, ← map_natCast (algebraMap (normInteger ℂ_[p]) _)]
    exact IsLocalization.Away.algebraMap_isUnit _
  have h2 : fontaineThetaInvertP (normInteger ℂ_[p]) p a = 0 ↔
      fontaineThetaInvertP (normInteger ℂ_[p]) p (algebraMap _ 𝔸 y) = 0 := by
    rw [← hy, map_mul, map_pow, (hU.pow N).mul_left_eq_zero]
  rw [h1, h2, thetaXi_algebraMap_eq_zero_iff, fontaineThetaInvertP_algebraMap_eq_zero_iff,
    ← RingHom.mem_ker, ker_theta_eq_span_xiA]

theorem thetaXi_surjective : Function.Surjective (thetaXi p) := by
  intro w
  set π' := (𝓣).ptPi (isPrimOne_xi (p := p)) with hπ'
  have hπn : ‖π'‖ = (p : ℝ)⁻¹ := by rw [hπ', norm_ptPi]; exact ptRad_xi
  have hπ0 : π' ≠ 0 := (𝓣).ptPi_ne_zero isPrimOne_xi
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖w‖ + 1)⁻¹ by positivity)
    (inv_p_lt_one (p := p))
  have hle : ‖w * π' ^ k‖ ≤ 1 := by
    rw [norm_mul, norm_pow, hπn]
    have h1 : ‖w‖ * (p : ℝ)⁻¹ ^ k ≤ ‖w‖ * (‖w‖ + 1)⁻¹ :=
      mul_le_mul_of_nonneg_left hk.le (norm_nonneg w)
    have h2 : ‖w‖ * (‖w‖ + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
    linarith
  obtain ⟨q, hq⟩ := (𝓣).exists_toUntiltField_eq isPrimOne_xi hle
  obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨y, hy⟩ := Y.2
  have hY : Y = ⟨incl ℂ_[p] p y, incl_mem_int y⟩ := Subtype.ext hy.symm
  refine ⟨algebraMap _ 𝔸 y * IsLocalization.Away.invSelf (p : AInf ℂ_[p] p) ^ k, ?_⟩
  have h1 : thetaXi p (algebraMap _ 𝔸 y) = w * π' ^ k := by
    rw [thetaXi_algebraMap, ← hY]; exact hq
  have h2 : thetaXi p (IsLocalization.Away.invSelf (p : AInf ℂ_[p] p)) = π'⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [hπ', ← thetaXi_algebraMap_p, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  rw [map_mul, map_pow, h1, h2, mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ0, one_pow, mul_one]

variable {ρ : Set.Ioo (0 : ℝ) 1}

theorem ptRad_xi_le (hρ : (p : ℝ)⁻¹ < ρ) : (𝓣).ptRad (xi p) ≤ ρ := by
  rw [ptRad_xi]; exact hρ.le

theorem exists_sub_awayToExt_mem_span (hρ : (p : ℝ)⁻¹ < ρ) (x : (𝓣).RobbaExt ρ) :
    ∃ a : 𝔸, x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} := by
  obtain ⟨a, ha⟩ := thetaXi_surjective ((𝓣).ptEval isPrimOne_xi (ptRad_xi_le hρ) x)
  refine ⟨a, Ideal.mem_span_singleton'.2 ?_⟩
  obtain ⟨y, hy⟩ := ((𝓣).ptEval_eq_zero_iff isPrimOne_xi (ptRad_xi_le hρ)
    (x - awayToExt p ρ a)).1 (by rw [map_sub, ptEval_awayToExt, ha, sub_self])
  exact ⟨y, by rw [hy, mul_comm]⟩

theorem awayToExt_mem_span_iff (hρ : (p : ℝ)⁻¹ < ρ) (a : 𝔸) :
    awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ↔ a ∈ 𝔍 := by
  rw [← thetaXi_eq_zero_iff, ← ptEval_awayToExt (ptRad_xi_le hρ),
    (𝓣).ptEval_eq_zero_iff isPrimOne_xi (ptRad_xi_le hρ), Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [← hy, mul_comm]⟩
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [hy, mul_comm]⟩

theorem awayToExt_mem_pow_iff (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (a : 𝔸) :
    awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m ↔ a ∈ 𝔍 ^ m := by
  set ξ := (𝓣).ξExt (xi p) ρ with hξdef
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [Ideal.span_singleton_pow, ker_pow_eq_span, Ideal.mem_span_singleton',
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, hy⟩
      have hm : awayToExt p ρ a ∈ Ideal.span {ξ} ^ m := by
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
        exact ⟨y * ξ, by rw [← hy, pow_succ]; ring⟩
      have hm' := (ih a).1 hm
      rw [ker_pow_eq_span, Ideal.mem_span_singleton'] at hm'
      obtain ⟨c, rfl⟩ := hm'
      have h2 : awayToExt p ρ c = y * ξ := by
        rw [map_mul, map_pow, awayToExt_xiA, pow_succ] at hy
        apply mul_right_cancel₀ (pow_ne_zero m (ξExt_ne_zero ρ))
        rw [← hy]; ring
      have h3 : c ∈ 𝔍 := (awayToExt_mem_span_iff hρ c).1 (Ideal.mem_span_singleton'.2 ⟨y, h2.symm⟩)
      rw [ker_eq_span_xiA, Ideal.mem_span_singleton'] at h3
      obtain ⟨d, rfl⟩ := h3
      exact ⟨d, by ring⟩
    · rintro ⟨c, rfl⟩
      exact ⟨awayToExt p ρ c, by rw [map_mul, map_pow, awayToExt_xiA]⟩

theorem exists_sub_awayToExt_mem_pow (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (x : (𝓣).RobbaExt ρ) :
    ∃ a : 𝔸, x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  set ξ := (𝓣).ξExt (xi p) ρ with hξdef
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨b, hb⟩ := exists_sub_awayToExt_mem_span hρ y
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hb
    refine ⟨a + b * algebraMap _ 𝔸 (xiA p) ^ m, ?_⟩
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨z, ?_⟩
    rw [map_add, map_mul, map_pow, awayToExt_xiA, pow_succ]
    linear_combination ξ ^ m * hz + hy

theorem exists_awayToExt_sub_mem_pow (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (x : (𝓣).RobbaExt ρ) :
    ∃ a : 𝔸, awayToExt p ρ a - x ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  obtain ⟨a, ha⟩ := exists_sub_awayToExt_mem_pow hρ m x
  refine ⟨a, ?_⟩
  set ξ := (𝓣).ξExt (xi p) ρ with hξdef
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha ⊢
  obtain ⟨y, hy⟩ := ha
  exact ⟨-y, by linear_combination -hy⟩

theorem ker_pow_le_comap (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    𝔍 ^ m ≤ (Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m).comap (awayToExt p ρ) := by
  rw [ker_pow_eq_span, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    map_pow, awayToExt_xiA, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

variable (p) in

def jetMap (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    𝔸 ⧸ 𝔍 ^ m →+* (𝓣).RobbaExt ρ ⧸ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m :=
  Ideal.quotientMap _ (awayToExt p ρ) (ker_pow_le_comap ρ m)

theorem jetMap_mk (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) (a : 𝔸) :
    jetMap p ρ m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (awayToExt p ρ a) :=
  Ideal.quotientMap_mk

theorem jetMap_mk_eq_mk_iff (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) (a : 𝔸) (x : (𝓣).RobbaExt ρ) :
    jetMap p ρ m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ x ↔
      awayToExt p ρ a - x ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  rw [jetMap_mk]
  exact Ideal.Quotient.eq

theorem jetMap_bijective (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) : Function.Bijective (jetMap p ρ m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [jetMap_mk, Ideal.Quotient.eq_zero_iff_mem, awayToExt_mem_pow_iff hρ] at hq
    exact Ideal.Quotient.eq_zero_iff_mem.2 hq
  · intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := exists_awayToExt_sub_mem_pow hρ m x
    exact ⟨Ideal.Quotient.mk (𝔍 ^ m) a, (jetMap_mk_eq_mk_iff ρ m a x).2 ha⟩

variable (p) in

def jetEquiv (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) :
    (𝔸 ⧸ 𝔍 ^ m) ≃+* ((𝓣).RobbaExt ρ ⧸ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m) :=
  RingEquiv.ofBijective (jetMap p ρ m) (jetMap_bijective hρ m)

variable (p) in

def iotaQ (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) : (𝓣).RobbaExt ρ →+* 𝔸 ⧸ 𝔍 ^ m :=
  (jetEquiv p hρ m).symm.toRingHom.comp (Ideal.Quotient.mk _)

theorem iotaQ_eq_mk_iff (hρ : (p : ℝ)⁻¹ < ρ) {m : ℕ} {x : (𝓣).RobbaExt ρ} {a : 𝔸} :
    iotaQ p hρ m x = Ideal.Quotient.mk _ a ↔
      x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  have e : (jetEquiv p hρ m) (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (awayToExt p ρ a) :=
    jetMap_mk ρ m a
  show (jetEquiv p hρ m).symm (Ideal.Quotient.mk _ x) = _ ↔ _
  rw [RingEquiv.symm_apply_eq, e]
  exact Ideal.Quotient.eq

theorem iotaQ_compat (hρ : (p : ℝ)⁻¹ < ρ) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow 𝔍 hle).comp (iotaQ p hρ n) = iotaQ p hρ m := by
  ext x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (iotaQ p hρ n x)
  rw [RingHom.comp_apply, ← ha]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [eq_comm, iotaQ_eq_mk_iff]
  exact Ideal.pow_le_pow_right hle ((iotaQ_eq_mk_iff hρ).1 ha.symm)

variable (p) in

def iota (hρ : (p : ℝ)⁻¹ < ρ) : (𝓣).RobbaExt ρ →+* 𝔹 :=
  _root_.AdicCompletion.liftRingHom 𝔍 (iotaQ p hρ) fun hle => iotaQ_compat hρ hle

theorem evalB_iota (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (x : (𝓣).RobbaExt ρ) :
    evalB ℂ_[p] p m (iota p hρ x) = iotaQ p hρ m x :=
  _root_.AdicCompletion.evalₐ_liftRingHom _ _ _ m x

theorem evalB_iota_eq_mk_iff (hρ : (p : ℝ)⁻¹ < ρ) {m : ℕ} {x : (𝓣).RobbaExt ρ} {a : 𝔸} :
    evalB ℂ_[p] p m (iota p hρ x) = Ideal.Quotient.mk _ a ↔
      x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  rw [evalB_iota, iotaQ_eq_mk_iff]

theorem iota_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (hρ1 : (p : ℝ)⁻¹ < ρ1) (h : (ρ1 : ℝ) ≤ ρ0)
    (x : (𝓣).RobbaExt ρ0) :
    iota p hρ1 ((𝓣).res h x) = iota p (hρ1.trans_le h) x := by
  refine evalB_ext fun m => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalB ℂ_[p] p m (iota p (hρ1.trans_le h) x))
  rw [← ha, evalB_iota_eq_mk_iff]
  have h2 := (evalB_iota_eq_mk_iff (hρ1.trans_le h)).1 ha.symm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2 ⊢
  obtain ⟨y, hy⟩ := h2
  refine ⟨(𝓣).res h y, ?_⟩
  rw [← res_awayToExt h, ← map_sub, ← hy, map_mul, map_pow, res_ξExt]

variable (p) in

def pUnit : 𝔸ˣ := (IsLocalization.Away.algebraMap_isUnit (p : AInf ℂ_[p] p)).unit

def InDom (x : (𝓣).RobbaTilde) : Prop :=
  ∃ ρ : Set.Ioo (0 : ℝ) 1, (p : ℝ)⁻¹ < ρ ∧ ∃ y : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ y = x

theorem exists_common {x y : (𝓣).RobbaTilde} (hx : InDom x) (hy : InDom y) :
    ∃ (ρ : Set.Ioo (0 : ℝ) 1) (_ : (p : ℝ)⁻¹ < ρ) (x' y' : (𝓣).RobbaExt ρ),
      (𝓣).ofRad ρ x' = x ∧ (𝓣).ofRad ρ y' = y := by
  obtain ⟨ρ1, h1, x1, rfl⟩ := hx
  obtain ⟨ρ2, h2, y2, rfl⟩ := hy
  let ρ3 : Set.Ioo (0 : ℝ) 1 := ⟨min ρ1 ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩
  exact ⟨ρ3, lt_min h1 h2, (𝓣).res (ρ1 := ρ3) (min_le_left _ _) x1,
    (𝓣).res (ρ1 := ρ3) (min_le_right _ _) y2, (𝓣).ofRad_res _ _, (𝓣).ofRad_res _ _⟩

variable (p) in

def rhoMid : Set.Ioo (0 : ℝ) 1 :=
  ⟨(1 + (p : ℝ)⁻¹) / 2, by have := inv_p_pos (p := p); positivity,
    by have := inv_p_lt_one (p := p); linarith⟩

theorem inv_p_lt_rhoMid : (p : ℝ)⁻¹ < rhoMid p := by
  show (p : ℝ)⁻¹ < (1 + (p : ℝ)⁻¹) / 2
  have := inv_p_lt_one (p := p); linarith

variable (p) in

def tildeDom : Subring (𝓣).RobbaTilde where
  carrier := {x | InDom x}
  mul_mem' {x y} hx hy := by
    obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
    exact ⟨ρ, hρ, x' * y', map_mul _ _ _⟩
  one_mem' := ⟨rhoMid p, inv_p_lt_rhoMid, 1, map_one _⟩
  add_mem' {x y} hx hy := by
    obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
    exact ⟨ρ, hρ, x' + y', map_add _ _ _⟩
  zero_mem' := ⟨rhoMid p, inv_p_lt_rhoMid, 0, map_zero _⟩
  neg_mem' {x} hx := by
    obtain ⟨ρ, hρ, x', rfl⟩ := hx
    exact ⟨ρ, hρ, -x', map_neg _ _⟩

theorem iota_eq_of_ofRad_eq {ρ1 ρ2 : Set.Ioo (0 : ℝ) 1} (h1 : (p : ℝ)⁻¹ < ρ1) (h2 : (p : ℝ)⁻¹ < ρ2)
    {y1 : (𝓣).RobbaExt ρ1} {y2 : (𝓣).RobbaExt ρ2} (h : (𝓣).ofRad ρ1 y1 = (𝓣).ofRad ρ2 y2) :
    iota p h1 y1 = iota p h2 y2 := by
  let ρ3 : Set.Ioo (0 : ℝ) 1 := ⟨min ρ1 ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩
  have h3 : (p : ℝ)⁻¹ < ρ3 := lt_min h1 h2
  have e : (𝓣).res (ρ1 := ρ3) (min_le_left _ _) y1 = (𝓣).res (ρ1 := ρ3) (min_le_right _ _) y2 :=
    (𝓣).ofRad_injective ρ3 (by rw [(𝓣).ofRad_res, (𝓣).ofRad_res, h])
  rw [← iota_res h3 (min_le_left _ _), e, iota_res h3 (min_le_right _ _)]

open Classical in
variable (p) in

def iotaTildeFun (x : (𝓣).RobbaTilde) : 𝔹 :=
  if h : InDom x then iota p h.choose_spec.1 h.choose_spec.2.choose else 0

theorem iotaTildeFun_ofRad (hρ : (p : ℝ)⁻¹ < ρ) (y : (𝓣).RobbaExt ρ) :
    iotaTildeFun p ((𝓣).ofRad ρ y) = iota p hρ y := by
  have h : InDom ((𝓣).ofRad ρ y) := ⟨ρ, hρ, y, rfl⟩
  rw [iotaTildeFun, dif_pos h]
  exact iota_eq_of_ofRad_eq _ _ h.choose_spec.2.choose_spec

theorem iotaTildeFun_one : iotaTildeFun p 1 = 1 := by
  have e : (1 : (𝓣).RobbaTilde) = (𝓣).ofRad (rhoMid p) 1 := (map_one _).symm
  rw [e, iotaTildeFun_ofRad inv_p_lt_rhoMid, map_one]

theorem iotaTildeFun_zero : iotaTildeFun p 0 = 0 := by
  have e : (0 : (𝓣).RobbaTilde) = (𝓣).ofRad (rhoMid p) 0 := (map_zero _).symm
  rw [e, iotaTildeFun_ofRad inv_p_lt_rhoMid, map_zero]

theorem iotaTildeFun_mul {x y : (𝓣).RobbaTilde} (hx : x ∈ tildeDom p) (hy : y ∈ tildeDom p) :
    iotaTildeFun p (x * y) = iotaTildeFun p x * iotaTildeFun p y := by
  obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
  rw [← map_mul, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, map_mul]

theorem iotaTildeFun_add {x y : (𝓣).RobbaTilde} (hx : x ∈ tildeDom p) (hy : y ∈ tildeDom p) :
    iotaTildeFun p (x + y) = iotaTildeFun p x + iotaTildeFun p y := by
  obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
  rw [← map_add, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, map_add]

variable (p) in

def iotaTilde : tildeDom p →+* 𝔹 where
  toFun x := iotaTildeFun p x
  map_one' := iotaTildeFun_one
  map_mul' x y := iotaTildeFun_mul x.2 y.2
  map_zero' := iotaTildeFun_zero
  map_add' x y := iotaTildeFun_add x.2 y.2

variable (p) in

def phiNeg (n : ℕ) : (𝓣).RobbaTilde →+* (𝓣).RobbaTilde := (frob ℂ_[p] p).tildeFrobSymm ^ n

variable (p) in

def iotaN (n : ℕ) (x : (𝓣).RobbaTilde) : 𝔹 := iotaTildeFun p (phiNeg p n x)

end WAEval

end GroundTheory.PAdicHodge
