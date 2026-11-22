import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors
open NumberField Complex GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.RealMult GlobalTheory.LatJet

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

def pairAct (a b c d : F) (p : F × F) : F × F := (p.2 * b + p.1 * d, p.2 * a + p.1 * c)

def pairInv (a b c d : F) (q : F × F) : F × F := (q.1 * a - q.2 * b, q.2 * d - q.1 * c)

theorem pairInv_act (a b c d : F) (h : a * d - b * c = 1) (p : F × F) :
    pairInv a b c d (pairAct a b c d p) = p := by
  ext
  · simp only [pairInv, pairAct]; linear_combination p.1 * h
  · simp only [pairInv, pairAct]; linear_combination p.2 * h

theorem pairAct_inv (a b c d : F) (h : a * d - b * c = 1) (q : F × F) :
    pairAct a b c d (pairInv a b c d q) = q := by
  ext
  · simp only [pairInv, pairAct]; linear_combination q.1 * h
  · simp only [pairInv, pairAct]; linear_combination q.2 * h

theorem int_of_mul_mem (I : FractionalIdeal (𝓞 F)⁰ F) (hI : I ≠ 0) (x : F) (h : ∀ y ∈ I, x * y ∈ I) :
    ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = x := by
  have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ x * I ≤ I := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact (I : Submodule (𝓞 F) F).smul_mem r (h j hj)
  have h2 := mul_le_mul_left h1 I⁻¹
  simp only [mul_assoc, mul_inv_cancel₀ hI, mul_one] at h2
  have h3 : x ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := h2 (FractionalIdeal.mem_spanSingleton_self _ x)
  exact (FractionalIdeal.mem_one_iff _).1 h3

theorem mul_mem_of_int (I : FractionalIdeal (𝓞 F)⁰ F) {x y : F} (hx : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = x)
    (hy : y ∈ I) : x * y ∈ I := by
  obtain ⟨r, rfl⟩ := hx
  rw [← Algebra.smul_def]
  exact (I : Submodule (𝓞 F) F).smul_mem r hy

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

theorem mem_dual_iff_latM (𝔞 : Frac F) (x : F) : x ∈ dualLat 𝔞 ↔ x ∈ latM 𝔞 := by
  rw [latM_eq_dual]; rfl

theorem dualLat_ne_zero (𝔞 : Frac F) : dualLat 𝔞 ≠ 0 := by
  rw [dualLat, ← latM_eq_dual, latM]
  refine mul_ne_zero (inv_ne_zero ?_) (Units.ne_zero _)
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

variable {𝔞 𝔟 : Frac F} {a b c d : F}

theorem a_int (h : InModularGroup 𝔞 𝔟 a b c d) : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a :=
  int_of_mul_mem (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (Units.ne_zero _) a fun y hy ↦ by
    have := (h.2 y hy 0 (dualLat 𝔞 : Submodule (𝓞 F) F).zero_mem).1
    simpa [mul_comm] using this

theorem d_int (h : InModularGroup 𝔞 𝔟 a b c d) : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = d :=
  int_of_mul_mem (dualLat 𝔞) (dualLat_ne_zero 𝔞) d fun y hy ↦ by
    have := (h.2 0 (zero_mem _) y hy).2
    simpa [mul_comm] using this

def latEquiv (h : InModularGroup 𝔞 𝔟 a b c d) : LatPair 𝔞 𝔟 ≃ LatPair 𝔞 𝔟 where
  toFun p := ⟨pairAct a b c d p.1, by
    obtain ⟨h1, h2⟩ := h.2 p.1.2 p.2.2.1 p.1.1 ((mem_dual_iff_latM 𝔞 _).2 p.2.1)
    refine ⟨(mem_dual_iff_latM 𝔞 _).1 h2, h1, fun h0 ↦ p.2.2.2 ?_⟩
    rw [← pairInv_act a b c d h.1 p.1, h0]; simp [pairInv]⟩
  invFun q := ⟨pairInv a b c d q.1, by
    have hm := (mem_dual_iff_latM 𝔞 _).2 q.2.1
    have hb := q.2.2.1
    refine ⟨(mem_dual_iff_latM 𝔞 _).1 ?_, ?_, fun h0 ↦ q.2.2.2 ?_⟩
    · refine (dualLat 𝔞 : Submodule (𝓞 F) F).sub_mem (mul_comm a q.1.1 ▸ mul_mem_of_int _ (a_int h) hm) ?_
      simpa using (h.2 q.1.2 hb 0 (dualLat 𝔞 : Submodule (𝓞 F) F).zero_mem).2
    · refine (𝔟 : Submodule (𝓞 F) F).sub_mem (mul_comm d q.1.2 ▸ mul_mem_of_int (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (d_int h) hb) ?_
      simpa using (h.2 0 (zero_mem _) q.1.1 hm).1
    · rw [← pairAct_inv a b c d h.1 q.1, h0]; simp [pairAct]⟩
  left_inv p := Subtype.ext (pairInv_act a b c d h.1 p.1)
  right_inv q := Subtype.ext (pairAct_inv a b c d h.1 q.1)

theorem latEquiv_apply (h : InModularGroup 𝔞 𝔟 a b c d) (p : LatPair 𝔞 𝔟) :
    (latEquiv h p).1 = pairAct a b c d p.1 := rfl

def clsEquiv (h : InModularGroup 𝔞 𝔟 a b c d) : Quotient (latRel 𝔞 𝔟) ≃ Quotient (latRel 𝔞 𝔟) :=
  Quotient.congr (latEquiv h) fun p q ↦ by
    show (∃ ε : (𝓞 F)ˣ, _) ↔ (∃ ε : (𝓞 F)ˣ, _)
    simp only [latEquiv_apply, pairAct]
    constructor
    · rintro ⟨ε, h1, h2⟩
      exact ⟨ε, by rw [h1, h2]; ring, by rw [h1, h2]; ring⟩
    · rintro ⟨ε, h1, h2⟩
      have hd := h.1
      exact ⟨ε, by linear_combination a * h1 - b * h2 + (((ε : 𝓞 F) : F) * p.1.1 - q.1.1) * hd,
        by linear_combination d * h2 - c * h1 + (((ε : 𝓞 F) : F) * p.1.2 - q.1.2) * hd⟩

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

end GlobalTheory.EisModular
