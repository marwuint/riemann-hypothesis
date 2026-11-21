import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable {g : ℕ} [Fact g.Prime]

theorem eq_one_of_cong (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hc : l.Coprime g)
    {u : Ω} (hu : u ^ l = 1) (h1 : A.valuation (u - 1) < 1) : u = 1 := by
  have hg : g.Prime := Fact.out
  by_contra hne
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [Nat.Coprime, Nat.gcd_zero_left] at hc
    exact hg.ne_one hc
  have hv : A.valuation u ≤ 1 := by
    have := A.valuation.map_add (u - 1) 1
    rw [sub_add_cancel, map_one] at this
    exact this.trans (max_le h1.le le_rfl)
  have hs : ∑ i ∈ Finset.range l, u ^ i = 0 := by
    have e := geom_sum_mul u l
    rw [hu, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr hne)
  have hlv : A.valuation (l : Ω) < 1 := by
    have e : (l : Ω) = -∑ i ∈ Finset.range l, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hs]
      simp
    rw [e, Valuation.map_neg]
    exact Valuation.map_sum_lt _ one_ne_zero fun i _ => by
      simpa using GlobalTheory.WeilDeligne.cong_pow hv (by simp) h1 i
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hw]
    have : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by
      rw [show Nat.card (𝓞 E ⧸ w.asIdeal) = normV w from rfl, hw]
      exact hg.ne_zero)
    rw [show normV w = Nat.card (𝓞 E ⧸ w.asIdeal) from rfl, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    intro hl
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hc).map (Int.castRingHom (𝓞 E))
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      rw [← hab]
      simp only [eq_intCast, Int.cast_natCast]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hl) (w.asIdeal.mul_mem_left b hgw)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := GlobalTheory.InertiaMovesRoot.val_eq_one_of_notMem h hlw
  have e : algebraMap E Ω ((((l : ℕ) : 𝓞 E)) : E) = (l : Ω) := by simp
  rw [e] at this
  exact (ne_of_lt hlv) this

theorem weil_fix (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1)
    (σ : Weil h) {ζ : Ω} (hζ : ζ ^ l = 1) : (σ : G E Ω) ζ = ζ := by
  have hg : g.Prime := Fact.out
  have hg2 := hg.two_le
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hl
    omega
  have hlg : l.Coprime g := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg).2 fun hd => ?_)
    have := Nat.le_of_dvd (by omega) (hd.trans hl)
    omega
  have key : ∀ (y : Ω), y ^ l = 1 → ∀ k : ℕ, y ^ (g ^ k) = y := by
    intro y hy k
    have hpos : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
    have hd : l ∣ g ^ k - 1 := by
      have := ((Nat.modEq_iff_dvd' (by omega : 1 ≤ g)).mpr hl).pow k
      rw [one_pow] at this
      exact (Nat.modEq_iff_dvd' hpos).mp this
    obtain ⟨m, hm⟩ := hd
    have : g ^ k = l * m + 1 := by omega
    rw [this, pow_succ, pow_mul, hy, one_pow, one_mul]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0] at hζ
    exact zero_ne_one hζ
  have hσζ : ((σ : G E Ω) ζ) ^ l = 1 := by rw [← map_pow, hζ, map_one]
  have hv1 : A.valuation ζ = 1 := by
    have e : A.valuation ζ ^ l = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hlt | heq | hgt
    · exfalso
      have : A.valuation ζ ^ l < 1 := by
        exact pow_lt_one' hlt hl0
      exact (ne_of_lt this) e
    · exact heq
    · exfalso
      have : 1 < A.valuation ζ ^ l := by
        exact one_lt_pow' hgt hl0
      exact (ne_of_gt this) e
  obtain ⟨a, b, hab⟩ := (mem_Weil h).mp σ.2
  have hc := hab.2 ζ hv1.le
  rw [hw, key _ hσζ, key _ hζ] at hc
  have hσ0 : (σ : G E Ω) ζ ≠ 0 := (_root_.map_ne_zero _).2 hζ0
  have hq : (σ : G E Ω) ζ / ζ = 1 := by
    refine eq_one_of_cong h hw hlg (by rw [div_pow, hσζ, hζ, div_one]) ?_
    rw [show (σ : G E Ω) ζ / ζ - 1 = ((σ : G E Ω) ζ - ζ) / ζ by field_simp, map_div₀, hv1, div_one]
    exact hc
  exact (div_eq_one_iff_eq hζ0).mp hq

def kummer (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1) (ι : Ω →+* ℂ)
    {x : Ω} (h0 : x ≠ 0) {a : E} (hx : x ^ l = algebraMap E Ω a) : Weil h →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun σ => ι ((σ : G E Ω) x / x)
      map_one' := by simp [div_self h0]
      map_mul' := fun σ σ' => by
        have h1 : ((σ' : G E Ω) x / x) ^ l = 1 := by
          rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, ← hx, div_self (pow_ne_zero _ h0)]
        have h2 := weil_fix h hw hl σ h1
        have h3 : (σ : G E Ω) x ≠ 0 := (_root_.map_ne_zero _).2 h0
        rw [← map_mul, ← h2, map_div₀ (σ : G E Ω)]
        congr 1
        show (σ : G E Ω) ((σ' : G E Ω) x) / x = _
        field_simp }

theorem kummer_apply (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1)
    (ι : Ω →+* ℂ) {x : Ω} (h0 : x ≠ 0) {a : E} (hx : x ^ l = algebraMap E Ω a) (σ : Weil h) :
    (kummer h hw hl ι h0 hx σ : ℂ) = ι ((σ : G E Ω) x / x) := rfl

end GlobalTheory.WeilDeligne.LabModel
