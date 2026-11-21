import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.PairFourier

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem tsum_natCast_eq {ι : Type} (n : ι → ℕ) (h : Summable (fun i ↦ (n i : ℂ))) :
    ∃ m : ℕ, ∑' i, (n i : ℂ) = m := by
  have hfin : (Function.support n).Finite := by
    have ht := h.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, ‖(n i : ℂ)‖ < 1 := by
      have := ht.norm
      simp only [norm_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    refine (Filter.eventually_cofinite.1 hev).subset ?_
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_setOf_eq, not_lt]
    have : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    simpa [Complex.norm_natCast] using this
  refine ⟨∑ i ∈ hfin.toFinset, n i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hi
    simp [hi]

variable {F : Type} [Field F] [NumberField F]

theorem norm_div_eq_nat (𝔞 : Frac F) {ν : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ m : ℕ, |((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞 = m := by
  set J : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) with hJdef
  have hle : J ≤ 1 := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hν
    calc J ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
          mul_le_mul_left h1 _
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJa : J * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ ν := by
    rw [hJdef, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hn := congrArg FractionalIdeal.absNorm hJa
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, ← hI, FractionalIdeal.coeIdeal_absNorm] at hn
  have h0 : (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact Units.ne_zero 𝔞
  refine ⟨Ideal.absNorm I, ?_⟩
  unfold nrm
  rw [div_eq_iff (by exact_mod_cast h0)]
  have := congrArg (fun q : ℚ ↦ (q : ℝ)) hn
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] at this
  rw [← this]

variable [IsTotallyReal F]

def pairPt (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) :=
  ⟨c.out.1.1 * c.out.1.2, by
    show _ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
    rw [Units.val_mul]
    exact FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1⟩

def pairCoef (𝔞 𝔟 : Frac F) (k : ℕ) (c : Quotient (qRel 𝔞 𝔟)) : ℕ :=
  (norm_div_eq_nat 𝔞 c.out.2.1).choose ^ (k - 1)

theorem qClass_eq (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) :
    qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * GlobalTheory.RealMult.qPower ((pairPt 𝔞 𝔟 c : F)) z := by
  unfold qClass qTerm pairCoef pairPt
  have hs := (norm_div_eq_nat 𝔞 c.out.2.1).choose_spec
  generalize (norm_div_eq_nat 𝔞 c.out.2.1).choose = m at hs ⊢
  rw [hs]
  push_cast
  rfl

theorem pairPt_ne_zero (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : pairPt 𝔞 𝔟 c ≠ 0 := by
  intro h
  have h' : c.out.1.1 * c.out.1.2 = 0 := congrArg Subtype.val h
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have := c.out.2.2.2 hr.embedding
  rw [h', map_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.PairFourier
