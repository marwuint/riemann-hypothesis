import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilTranslate
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilFixedField

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine AddSubgroup

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

local notation "ι" => algebraMap F W.toAffine.FunctionField

theorem divisorOf_pow {f : W.toAffine.FunctionField} (hf : f ≠ 0) (k : ℕ) :
    divisorOf W (f ^ k) = k • divisorOf W f := by
  induction k with
  | zero => rw [pow_zero, divisorOf_one, zero_smul]
  | succ k ih => rw [pow_succ, divisorOf_mul W (pow_ne_zero k hf) hf, ih, succ_nsmul]

theorem divisorOf_prod {ι' : Type*} (s : Finset ι') (φ : ι' → W.toAffine.FunctionField)
    (hφ : ∀ i ∈ s, φ i ≠ 0) : divisorOf W (∏ i ∈ s, φ i) = ∑ i ∈ s, divisorOf W (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, divisorOf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      divisorOf_mul W (hφ a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hφ i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hφ i (Finset.mem_insert_of_mem hi)]

def IsWeilData (n : ℕ) (T : W.toAffine.Point) (f g : W.toAffine.FunctionField) : Prop :=
  f ≠ 0 ∧ g ≠ 0 ∧ divisorOf W f = (n : ℤ) • (Finsupp.single T 1 - Finsupp.single 0 1) ∧
    ∃ hn : (n : ℤ) ≠ 0, mulPullback W n hn f = g ^ n

open Classical in

noncomputable def weilPairing (n : ℕ) (S T : W.toAffine.Point) : F :=
  if h : ∃ ζ : F, ∃ f g, IsWeilData W n T f g ∧ translate W S g = ι ζ * g then h.choose else 1

variable {W}

theorem IsWeilData.exists_translate_eq {n : ℕ} {T : W.toAffine.Point} {f g : W.toAffine.FunctionField}
    (h : IsWeilData W n T f g) {S : W.toAffine.Point} (hS : n • S = 0) :
    ∃ ζ : F, ζ ^ n = 1 ∧ translate W S g = ι ζ * g := by
  obtain ⟨hf, hg, -, hn0, hpull⟩ := h
  have hn : n ≠ 0 := by exact_mod_cast hn0
  have hS' : (n : ℤ) • S = 0 := by rw [natCast_zsmul]; exact hS
  have hpow : (translate W S g / g) ^ n = ι 1 := by
    rw [div_pow, ← map_pow, ← hpull, translate_mulPullback_of_zsmul_eq_zero W hn0 hS', hpull,
      div_self (pow_ne_zero n hg), map_one]
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_pow_eq W hn hpow
  refine ⟨d, ?_, ?_⟩
  · apply (algebraMap F W.toAffine.FunctionField).injective
    rw [map_pow, hd, hpow, map_one]
  · rw [hd, div_mul_cancel₀ _ hg]

theorem IsWeilData.exists_eq_mul {n : ℕ} {T : W.toAffine.Point} {f g f' g' : W.toAffine.FunctionField}
    (h : IsWeilData W n T f g) (h' : IsWeilData W n T f' g') : ∃ d : F, g' = ι d * g := by
  obtain ⟨hf, hg, hdiv, hn0, hpull⟩ := h
  obtain ⟨hf', hg', hdiv', hn0', hpull'⟩ := h'
  have hn : n ≠ 0 := by exact_mod_cast hn0
  obtain ⟨c, -, hc⟩ := exists_algebraMap_mul_eq_of_divisorOf_eq W hf hf' (hdiv.trans hdiv'.symm)
  have hpow : (g' / g) ^ n = ι c := by
    rw [div_pow, ← hpull', ← hc, map_mul, mulPullback_algebraMap, hpull,
      mul_div_cancel_right₀ _ (pow_ne_zero n hg)]
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_pow_eq W hn hpow
  exact ⟨d, by rw [hd, div_mul_cancel₀ _ hg]⟩

theorem translate_eq_weilPairing_mul {n : ℕ} {S T : W.toAffine.Point}
    {f g : W.toAffine.FunctionField} (hS : n • S = 0) (h : IsWeilData W n T f g) :
    translate W S g = ι (weilPairing W n S T) * g := by
  obtain ⟨ζ, -, hζ⟩ := h.exists_translate_eq hS
  have hex : ∃ ζ : F, ∃ f g, IsWeilData W n T f g ∧ translate W S g = ι ζ * g := ⟨ζ, f, g, h, hζ⟩
  classical
  rw [weilPairing, dif_pos hex]
  obtain ⟨f₀, g₀, h₀, hζ₀⟩ := hex.choose_spec
  obtain ⟨d, rfl⟩ := h₀.exists_eq_mul h
  rw [map_mul, translate_algebraMap, hζ₀]
  ring

theorem weilPairing_eq_of_translate_eq {n : ℕ} {S T : W.toAffine.Point}
    {f g : W.toAffine.FunctionField} (hS : n • S = 0) (h : IsWeilData W n T f g) {ζ : F}
    (hζ : translate W S g = ι ζ * g) : weilPairing W n S T = ζ := by
  have := (translate_eq_weilPairing_mul hS h).symm.trans hζ
  exact (algebraMap F W.toAffine.FunctionField).injective (mul_right_cancel₀ h.2.1 this)

variable (W)

theorem exists_isWeilData {n : ℕ} (hn : (n : F) ≠ 0) {T : W.toAffine.Point} (hT : n • T = 0) :
    ∃ f g, IsWeilData W n T f g := by
  classical
  have hn' : n ≠ 0 := by rintro rfl; simp at hn
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn'
  have hnF : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hT' : (n : ℤ) • T = 0 := by rw [natCast_zsmul]; exact hT

  obtain ⟨f, hf, hdivf⟩ := (exists_divisorOf_eq_iff W
    ((n : ℤ) • (Finsupp.single T 1 - Finsupp.single 0 1))).mpr ⟨by simp, by simp [hT]⟩

  obtain ⟨T', hT''⟩ := exists_zsmul_eq W hn0 T
  set K : Finset W.toAffine.Point := (finite_setOf_zsmul_eq W hnF 0).toFinset with hK
  have hmemK : ∀ R, R ∈ K ↔ (n : ℤ) • R = 0 := fun R => by simp [hK]
  have hcardK : K.card = n ^ 2 := by
    have h := card_zsmul_eq_zero W hnF
    rw [Int.natAbs_natCast] at h
    rw [← h, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun R => hmemK R)
  set D : CurveDivisor W := ∑ R ∈ K, (Finsupp.single (T' + R) 1 - Finsupp.single R 1) with hD
  have hDpull : D = mulPullbackDivisor W hnF (Finsupp.single T 1 - Finsupp.single 0 1) := by
    ext P
    rw [mulPullbackDivisor_apply, hD, Finsupp.finsetSum_apply]
    simp only [Finsupp.sub_apply, Finsupp.single_apply, Finset.sum_sub_distrib]
    have h1 : ∑ R ∈ K, (if T' + R = P then (1 : ℤ) else 0) =
        if (n : ℤ) • P = T then 1 else 0 := by
      have e : ∀ R, (T' + R = P) ↔ (R = P - T') := fun R => by
        constructor
        · rintro rfl; abel
        · rintro rfl; abel
      simp_rw [e]
      rw [Finset.sum_ite_eq' K (P - T') (fun _ => (1 : ℤ))]
      simp only [hmemK, zsmul_sub, hT'', sub_eq_zero]
    have h2 : ∑ R ∈ K, (if R = P then (1 : ℤ) else 0) = if (n : ℤ) • P = 0 then 1 else 0 := by
      rw [Finset.sum_ite_eq' K P (fun _ => (1 : ℤ))]
      simp only [hmemK]
    rw [h1, h2]
    simp only [eq_comm]
  have hdegD : divisorDegree W D = 0 := by
    rw [hD, map_sum]
    simp
  have hsumD : divisorSum W D = 0 := by
    rw [hD, map_sum]
    simp only [map_sub, divisorSum_single, one_smul, add_sub_cancel_right, Finset.sum_const,
      hcardK]
    have hT3 : n • T' = T := by rw [← natCast_zsmul]; exact hT''
    rw [pow_two, mul_nsmul, hT3, hT]
  obtain ⟨g₀, hg₀, hdivg₀⟩ := (exists_divisorOf_eq_iff W D).mpr ⟨hdegD, hsumD⟩

  have hdiv : divisorOf W (g₀ ^ n) = divisorOf W (mulPullback W n hn0 f) := by
    rw [divisorOf_pow W hg₀, divisorOf_mulPullback W hnF hn0 hf, hdivf, map_zsmul, ← hDpull,
      hdivg₀, natCast_zsmul]
  obtain ⟨c, hc0, hc⟩ := exists_algebraMap_mul_eq_of_divisorOf_eq W (pow_ne_zero n hg₀)
    (mulPullback_ne_zero W hn0 hf) hdiv
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hn')
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hn'] at hd
    exact hc0 hd.symm
  refine ⟨f, ι d * g₀, hf, mul_ne_zero ((map_ne_zero_iff _ (algebraMap F W.toAffine.FunctionField).injective).mpr hd0) hg₀, hdivf, hn0, ?_⟩
  rw [← hc, mul_pow, ← map_pow, hd]

variable {W}

theorem weilPairing_pow_eq_one {n : ℕ} (hn : (n : F) ≠ 0) {S T : W.toAffine.Point}
    (hS : n • S = 0) (hT : n • T = 0) : weilPairing W n S T ^ n = 1 := by
  obtain ⟨f, g, h⟩ := exists_isWeilData W hn hT
  obtain ⟨ζ, hζn, hζ⟩ := h.exists_translate_eq hS
  rw [weilPairing_eq_of_translate_eq hS h hζ, hζn]

theorem weilPairing_ne_zero {n : ℕ} (hn : (n : F) ≠ 0) {S T : W.toAffine.Point}
    (hS : n • S = 0) (hT : n • T = 0) : weilPairing W n S T ≠ 0 := by
  intro h0
  have h := weilPairing_pow_eq_one hn hS hT
  have hn' : n ≠ 0 := by rintro rfl; simp at hn
  rw [h0, zero_pow hn'] at h
  exact zero_ne_one h

noncomputable def weilPairingRoot {n : ℕ} (hn : (n : F) ≠ 0)
    (S T : torsionBy W.toAffine.Point n) : rootsOfUnity n F :=
  ⟨Units.mk0 (weilPairing W n S T)
      (weilPairing_ne_zero hn (torsionBy.nsmul_iff.mp S.2) (torsionBy.nsmul_iff.mp T.2)), by
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact weilPairing_pow_eq_one hn (torsionBy.nsmul_iff.mp S.2) (torsionBy.nsmul_iff.mp T.2)⟩

@[simp]
theorem coe_weilPairingRoot {n : ℕ} (hn : (n : F) ≠ 0) (S T : torsionBy W.toAffine.Point n) :
    ((weilPairingRoot hn S T : Fˣ) : F) = weilPairing W n S T :=
  rfl

end GroundTheory.Arith.Abelian
