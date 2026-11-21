import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit

theorem zeta_mem_of_dvd {F : IntermediateField ℚ ℂ} {a N : ℕ} (hN : N ≠ 0) (h : a ∣ N) (hF : zeta N ∈ F) :
    zeta a ∈ F := by
  obtain ⟨k, rfl⟩ := h
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hN)
  have : zeta a = zeta (a * k) ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem hF k

theorem zeta_lcm_mem {F : IntermediateField ℚ ℂ} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h₁ : zeta a ∈ F)
    (h₂ : zeta b ∈ F) : zeta (Nat.lcm a b) ∈ F := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hl : ((Nat.lcm a b : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero ha hb)
  have e1 : ((Nat.gcd a b : ℕ) : ℂ) * (Nat.lcm a b : ℕ) = a * b := by exact_mod_cast Nat.gcd_mul_lcm a b
  have e2 : ((Nat.gcd a b : ℕ) : ℂ) = a * (Nat.gcdA a b : ℂ) + b * (Nat.gcdB a b : ℂ) := by
    exact_mod_cast Nat.gcd_eq_gcd_ab a b
  have : zeta (Nat.lcm a b) = zeta a ^ Nat.gcdB a b * zeta b ^ Nat.gcdA a b := by
    rw [zeta, zeta, zeta, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    field_simp
    linear_combination (-1 : ℂ) * e1 + (Nat.lcm a b : ℂ) * e2
  rw [this]
  exact mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Idx (H : Host E) (p : ℕ) : Type := Σ l : {l : Level H // l.GoodAt p}, Coeff l.1

abbrev Idx.l {p : ℕ} (i : Idx H p) : Level H := i.1.1

abbrev Idx.F {p : ℕ} (i : Idx H p) : IntermediateField ℚ ℂ := i.2.F

def Idx.Le {p : ℕ} (i j : Idx H p) : Prop := i.l.Dvd j.l ∧ i.F ≤ j.F

theorem Idx.Le.refl {p : ℕ} (i : Idx H p) : i.Le i := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl⟩

theorem Idx.Le.trans {p : ℕ} {i j k : Idx H p} (h : i.Le j) (h' : j.Le k) : i.Le k :=
  ⟨⟨h.1.1.trans h'.1.1, h'.1.2.1.trans h.1.2.1, h.1.2.2.trans h'.1.2.2⟩, h.2.trans h'.2⟩

def addLevel (l : Level H) {N : ℕ} (hN : N ≠ 0) : Level H :=
  { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos (Nat.pos_of_ne_zero hN) }

theorem zeta_mem_sup (F : IntermediateField ℚ ℂ) (N : ℕ) :
    zeta N ∈ F ⊔ IntermediateField.adjoin ℚ {zeta N} :=
  (le_sup_right : _ ≤ F ⊔ _) (IntermediateField.subset_adjoin _ _ rfl)

def addCoeff {l : Level H} (c : Coeff l) {N : ℕ} (hN : N ≠ 0) : Coeff (addLevel l hN) :=
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hz : zeta (addLevel l hN).M' ∈ c.F ⊔ IntermediateField.adjoin ℚ {zeta N} := by
    have : (addLevel l hN).M' = Nat.lcm l.M' N := (Nat.lcm_assoc _ _ _).symm
    rw [this]
    exact zeta_lcm_mem hM' hN ((le_sup_left : c.F ≤ _) c.zeta_mem) (zeta_mem_sup _ _)
  { F := c.F ⊔ IntermediateField.adjoin ℚ {zeta N}
    fin := by
      have := c.fin
      have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta N}) :=
        IntermediateField.adjoin.finiteDimensional
          (((Complex.isPrimitiveRoot_exp N hN).isIntegral (Nat.pos_of_ne_zero hN)).tower_top)
      infer_instance
    conj := fun τ a => (le_sup_left : c.F ≤ _) (c.conj τ a)
    zeta_mem := hz
    le := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x (rfl | hx)
      · exact (le_sup_left : c.F ≤ _) (c.le (IntermediateField.subset_adjoin _ _ (by simp)))
      · obtain rfl : x = _ := hx
        exact zeta_mem_of_dvd
          (Nat.lcm_ne_zero (by have := l.three_le; change l.M ≠ 0; omega) (addLevel l hN).A_pos.ne')
          (Nat.dvd_lcm_right _ _) hz }

def Idx.add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : Idx H p :=
  ⟨⟨addLevel i.l hN, i.1.2⟩, addCoeff i.2 hN⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity
