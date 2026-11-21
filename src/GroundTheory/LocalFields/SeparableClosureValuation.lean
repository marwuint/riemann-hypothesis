import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.UnitsBasic
import GroundTheory.LocalFields.IntermediateField
import GroundTheory.LocalFields.SeparableClosure

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing
open scoped WithZero

section Valuation

variable {F G : Type*} [Field F] [ValuativeRel F] [Field G] [ValuativeRel G] [Algebra F G]
  [ValuativeExtension F G]

theorem valuation_algebraMap_eq_iff (x y : F) :
    valuation G (algebraMap F G x) = valuation G (algebraMap F G y) ↔
      valuation F x = valuation F y := by
  rw [le_antisymm_iff, le_antisymm_iff, ← (valuation G).vle_iff_le, ← (valuation G).vle_iff_le,
    ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle, (valuation F).vle_iff_le,
    (valuation F).vle_iff_le]

theorem valuation_algebraMap_le_iff (x y : F) :
    valuation G (algebraMap F G x) ≤ valuation G (algebraMap F G y) ↔
      valuation F x ≤ valuation F y := by
  rw [← (valuation G).vle_iff_le, ValuativeExtension.vle_iff_vle, (valuation F).vle_iff_le]

end Valuation

section Ord

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem ord_zero_alt : ord (0 : K) = 0 := by
  simp [ord]

@[simp]
theorem ord_one : ord (1 : K) = 0 := by
  simp [ord]

private theorem ord_pow_alt (x : K) (n : ℕ) : ord (x ^ n) = n * ord x := by
  simp [ord, WithZero.log_pow]

private theorem ord_zpow_alt (x : K) (n : ℤ) : ord (x ^ n) = n * ord x := by
  simp [ord, map_zpow₀, WithZero.log_zpow]

theorem ord_eq_ord_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord x = ord y ↔ valuation K x = valuation K y := by
  rw [← normalizedValuation_eq_iff, normalizedValuation_eq_exp_ord hx,
    normalizedValuation_eq_exp_ord hy, WithZero.exp_inj, neg_inj]

theorem ord_le_ord_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord x ≤ ord y ↔ valuation K y ≤ valuation K x := by
  rw [← normalizedValuation_le_iff, normalizedValuation_eq_exp_ord hx,
    normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp, neg_le_neg_iff]

variable (K) in

theorem exists_ord_eq (n : ℤ) : ∃ x : K, x ≠ 0 ∧ ord x = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨(ϖ : K) ^ n, zpow_ne_zero _ hϖ0, by rw [ord_zpow_alt, ord_uniformizer hϖ, mul_one]⟩

end Ord

section Extension

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

private theorem ord_algebraMap_eq_ramificationIndex_mul (a : K) : ord (algebraMap K L a) = ramificationIndex K L * ord a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero

  have hspan : Ideal.span {algebraMap 𝒪[K] 𝒪[L] ϖ} =
      Ideal.span {ϖL ^ ramificationIndex K L} := by
    rw [← Ideal.span_singleton_pow, ← hϖL.maximalIdeal_eq, ← map_maximalIdeal K L,
      hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hu' : algebraMap K L ϖ * ((u : 𝒪[L]) : L) = (ϖL : L) ^ ramificationIndex K L := by
    have := congrArg (fun z : 𝒪[L] ↦ (z : L)) hu
    simpa using this
  have hιϖ : algebraMap K L ϖ ≠ 0 := (_root_.map_ne_zero _).mpr hϖ0
  have hu0 : ((u : 𝒪[L]) : L) ≠ 0 := by
    have : (u : 𝒪[L]) ≠ 0 := u.ne_zero
    exact_mod_cast this
  have hkey : ord (algebraMap K L ϖ) = ramificationIndex K L := by
    have h := congrArg ord hu'
    rw [ord_mul hιϖ hu0, ord_unit, add_zero, ord_pow_alt, ord_uniformizer hϖL, mul_one] at h
    exact h

  rcases eq_or_ne a 0 with rfl | ha
  · simp [ord_zero_alt]
  have hk : (ϖ : K) ^ ord a ≠ 0 := zpow_ne_zero _ hϖ0
  have hv : valuation K a = valuation K ((ϖ : K) ^ ord a) := by
    rw [← ord_eq_ord_iff ha hk, ord_zpow_alt, ord_uniformizer hϖ, mul_one]
  have hvL : valuation L (algebraMap K L a) = valuation L (algebraMap K L ((ϖ : K) ^ ord a)) :=
    (valuation_algebraMap_eq_iff a _).mpr hv
  rw [← ord_eq_ord_iff ((_root_.map_ne_zero _).mpr ha) ((_root_.map_ne_zero _).mpr hk)] at hvL
  rw [hvL, map_zpow₀, ord_zpow_alt, hkey, mul_comm]

theorem valuation_pow_ramificationIndex_eq {y : L} {a : K} (hy : y ≠ 0) (ha : a ≠ 0)
    (h : ord a = ord y) :
    valuation L y ^ ramificationIndex K L = valuation L (algebraMap K L a) := by
  rw [← map_pow, ← ord_eq_ord_iff (pow_ne_zero _ hy) ((_root_.map_ne_zero _).mpr ha), ord_pow_alt,
    ord_algebraMap_eq_ramificationIndex_mul, h]

end Extension

section Structure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isNonarchimedeanLocalField_finiteExtensionStructure_top {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [v : ValuativeRel L] [ValuativeExtension K L] :
    @IsNonarchimedeanLocalField L _ v (finiteExtensionStructure K L).top := by
  have h1 : @IsNonarchimedeanLocalField L _ (finiteExtensionStructure K L).rel
      (finiteExtensionStructure K L).top :=
    finiteExtensionStructure_isNonarchimedeanLocalField K L
  rw [← valuativeRel_eq_finiteExtensionStructure K (L := L)] at h1
  exact h1

end Structure

section Rat

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]

open Classical in

def ordRat (x : Ω) : ℚ :=
  if h : ∃ p : ℕ × K, 0 < p.1 ∧ p.2 ≠ 0 ∧ valuation Ω x ^ p.1 = valuation Ω (algebraMap K Ω p.2)
  then (ord h.choose.2 : ℚ) / h.choose.1 else 0

variable {K}

omit [ValuativeExtension K Ω] in

theorem ordRat_congr {x y : Ω} (h : valuation Ω x = valuation Ω y) : ordRat K x = ordRat K y := by
  unfold ordRat
  rw [h]

theorem ordRat_eq_of_pow {x : Ω} {m : ℕ} {a : K} (hm : 0 < m) (ha : a ≠ 0)
    (h : valuation Ω x ^ m = valuation Ω (algebraMap K Ω a)) : ordRat K x = ord a / m := by
  have hex : ∃ p : ℕ × K, 0 < p.1 ∧ p.2 ≠ 0 ∧
      valuation Ω x ^ p.1 = valuation Ω (algebraMap K Ω p.2) := ⟨(m, a), hm, ha, h⟩
  rw [ordRat, dif_pos hex]
  obtain ⟨hp1, hp2, hp3⟩ := hex.choose_spec
  set p := hex.choose

  have hv : valuation Ω (algebraMap K Ω (p.2 ^ m)) = valuation Ω (algebraMap K Ω (a ^ p.1)) := by
    rw [map_pow, map_pow, map_pow, map_pow, ← hp3, ← h, ← pow_mul, ← pow_mul, mul_comm]
  rw [valuation_algebraMap_eq_iff, ← ord_eq_ord_iff (pow_ne_zero _ hp2) (pow_ne_zero _ ha),
    ord_pow_alt, ord_pow_alt] at hv
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hp1' : (p.1 : ℚ) ≠ 0 := by exact_mod_cast hp1.ne'
  rw [div_eq_div_iff hp1' hm']
  have hv' : ((m : ℤ) : ℚ) * (ord p.2 : ℚ) = ((p.1 : ℤ) : ℚ) * (ord a : ℚ) := by exact_mod_cast hv
  push_cast at hv'
  linarith

omit [ValuativeExtension K Ω] in

@[simp]
theorem ordRat_zero : ordRat K (0 : Ω) = 0 := by
  rw [ordRat, dif_neg]
  rintro ⟨p, hp1, hp2, hp3⟩
  rw [map_zero, zero_pow hp1.ne'] at hp3
  exact ((_root_.map_ne_zero _).mpr hp2) ((Valuation.zero_iff _).mp hp3.symm)

@[simp]
theorem ordRat_algebraMap (a : K) : ordRat K (algebraMap K Ω a) = ord a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [ord_zero_alt]
  · rw [ordRat_eq_of_pow one_pos ha (pow_one _), Nat.cast_one, div_one]

@[simp]
theorem ordRat_one : ordRat K (1 : Ω) = 0 := by
  rw [← map_one (algebraMap K Ω), ordRat_algebraMap, ord_one, Int.cast_zero]

theorem ordRat_algebraMap_of_finite {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [Algebra L Ω] [IsScalarTower K L Ω] [ValuativeExtension L Ω] (y : L) :
    ordRat K (algebraMap L Ω y) = ord y / ramificationIndex K L := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [ord_zero_alt]
  obtain ⟨a, ha, hay⟩ := exists_ord_eq K (ord y)
  have h := valuation_pow_ramificationIndex_eq K hy ha hay
  rw [← map_pow, ← valuation_algebraMap_eq_iff (G := Ω), map_pow, map_pow,
    ← IsScalarTower.algebraMap_apply] at h
  rw [ordRat_eq_of_pow (ramificationIndex_pos K L) ha h, hay]

variable [Algebra.IsAlgebraic K Ω]

theorem exists_valuation_pow_eq {x : Ω} (hx : x ≠ 0) :
    ∃ (m : ℕ) (a : K), 0 < m ∧ a ≠ 0 ∧ valuation Ω x ^ m = valuation Ω (algebraMap K Ω a) := by
  let L := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let : TopologicalSpace L := (finiteExtensionStructure K L).top
  have : IsNonarchimedeanLocalField L := isNonarchimedeanLocalField_finiteExtensionStructure_top K
  set y := IntermediateField.AdjoinSimple.gen K x
  have hyx : algebraMap L Ω y = x := IntermediateField.AdjoinSimple.algebraMap_gen K x
  have hy : y ≠ 0 := by
    rintro h
    rw [h, map_zero] at hyx
    exact hx hyx.symm
  obtain ⟨a, ha, hay⟩ := exists_ord_eq K (ord y)
  have h := valuation_pow_ramificationIndex_eq K hy ha hay
  rw [← map_pow, ← valuation_algebraMap_eq_iff (G := Ω), map_pow, map_pow,
    ← IsScalarTower.algebraMap_apply, hyx] at h
  exact ⟨ramificationIndex K L, a, ramificationIndex_pos K L, ha, h⟩

theorem ordRat_mul {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K (x * y) = ordRat K x + ordRat K y := by
  obtain ⟨m, a, hm, ha, h⟩ := exists_valuation_pow_eq (K := K) hx
  obtain ⟨n, b, hn, hb, h'⟩ := exists_valuation_pow_eq (K := K) hy
  have hab : a ^ n * b ^ m ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)
  have hxy : valuation Ω (x * y) ^ (m * n) = valuation Ω (algebraMap K Ω (a ^ n * b ^ m)) := by
    rw [map_mul, mul_pow, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, ← h, ← h',
      ← pow_mul, ← pow_mul, mul_comm n m]
  rw [ordRat_eq_of_pow (Nat.mul_pos hm hn) hab hxy, ordRat_eq_of_pow hm ha h,
    ordRat_eq_of_pow hn hb h', ord_mul (pow_ne_zero _ ha) (pow_ne_zero _ hb), ord_pow_alt, ord_pow_alt]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

theorem ordRat_le_ordRat_iff {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K x ≤ ordRat K y ↔ valuation Ω y ≤ valuation Ω x := by
  obtain ⟨m, a, hm, ha, h⟩ := exists_valuation_pow_eq (K := K) hx
  obtain ⟨n, b, hn, hb, h'⟩ := exists_valuation_pow_eq (K := K) hy
  have hmn : m * n ≠ 0 := (Nat.mul_pos hm hn).ne'
  have hp : valuation Ω y ^ (m * n) ≤ valuation Ω x ^ (m * n) ↔
      valuation Ω y ≤ valuation Ω x := pow_le_pow_iff_left₀ zero_le zero_le hmn
  rw [← hp]
  have e1 : valuation Ω x ^ (m * n) = valuation Ω (algebraMap K Ω (a ^ n)) := by
    rw [pow_mul, h, map_pow, map_pow]
  have e2 : valuation Ω y ^ (m * n) = valuation Ω (algebraMap K Ω (b ^ m)) := by
    rw [mul_comm, pow_mul, h', map_pow, map_pow]
  rw [e1, e2, valuation_algebraMap_le_iff, ← ord_le_ord_iff (pow_ne_zero _ ha) (pow_ne_zero _ hb),
    ordRat_eq_of_pow hm ha h, ordRat_eq_of_pow hn hb h', ord_pow_alt, ord_pow_alt]
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ hm' hn']
  constructor
  · intro hle
    have h2 : (((n : ℤ) * ord a : ℤ) : ℚ) ≤ (((m : ℤ) * ord b : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · intro hle
    have : ((n : ℤ) : ℚ) * ord a ≤ ((m : ℤ) : ℚ) * ord b := by exact_mod_cast hle
    push_cast at this
    linarith

theorem ordRat_eq_ordRat_iff {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K x = ordRat K y ↔ valuation Ω x = valuation Ω y := by
  rw [le_antisymm_iff, le_antisymm_iff, ordRat_le_ordRat_iff hx hy, ordRat_le_ordRat_iff hy hx,
    and_comm]

variable (K Ω) in

def ordRatHom : Ωˣ →* Multiplicative ℚ where
  toFun x := Multiplicative.ofAdd (ordRat K (x : Ω))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, ordRat_mul x.ne_zero y.ne_zero, ofAdd_add]

@[simp]
theorem toAdd_ordRatHom (x : Ωˣ) : (ordRatHom K Ω x).toAdd = ordRat K (x : Ω) := rfl

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [Algebra L Ω] [IsScalarTower K L Ω] [ValuativeExtension L Ω]

end Rat

end GroundTheory.LocalField
