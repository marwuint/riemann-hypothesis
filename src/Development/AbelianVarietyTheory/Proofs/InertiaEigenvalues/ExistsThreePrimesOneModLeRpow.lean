import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationComapLtOne

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (TwDatum Twisted SameBelow SamePair LiesUnder TwistedPlaceSettings namedPrimes expDat GoodDatum GoodSystem
  recorded ExistsChoice WithToricIntegralityConstant FamTwGood TwGoodClosed)

namespace GlobalTheory.TwistGoodCompare

variable {D : D7}

theorem twisted_iff (w : D.what₂.places.Pl) : Twisted D w ↔ TwistedAt D w := Iff.rfl

theorem val_int_nonneg (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : IsIntegral ℤ x) :
    0 ≤ D.what₂.places.val w x := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  rw [D.val_eq w x h0]
  have h1 : (D.plEq w).valuation D.what₂.LL x ≤ 1 := (D.plEq w).valuation_le_one (⟨x, hx⟩ : 𝓞 D.what₂.LL)
  have h2 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := by simpa using h0
  have h3 : WithZero.log ((D.plEq w).valuation D.what₂.LL x) ≤ 0 := by
    rw [← WithZero.log_one, WithZero.log_le_log h2 one_ne_zero]; exact h1
  have : 0 ≤ vAdd (D.plEq w) x := by unfold vAdd; omega
  exact_mod_cast this

theorem isIntegral_coe (x : 𝓞 ↥D.LL0) : IsIntegral ℤ ((x : ↥D.LL0) : D.what₂.LL) :=
  (RingOfIntegers.isIntegral_coe x).map (D.LL0.val.toRingHom.toIntAlgHom)

def below (w : D.what₂.places.Pl) : HeightOneSpectrum (𝓞 ↥D.LL0) where
  asIdeal :=
    { carrier := {x | 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        have := (D.what₂.places.val w).map_add ((a : ↥D.LL0) : D.what₂.LL) ((b : ↥D.LL0) : D.what₂.LL)
        exact lt_of_lt_of_le (lt_min ha hb) this
      smul_mem' := fun a b hb => by
        have := (D.what₂.places.val w).map_mul ((a : ↥D.LL0) : D.what₂.LL) ((b : ↥D.LL0) : D.what₂.LL)
        have h2 := lt_of_lt_of_le hb (le_add_of_nonneg_left (val_int_nonneg w (isIntegral_coe a)))
        rw [← this] at h2
        exact h2 }
  isPrime := by
    refine ⟨fun h => ?_, fun {a b} h => ?_⟩
    · rw [Ideal.eq_top_iff_one] at h
      have : 0 < D.what₂.places.val w (((1 : 𝓞 ↥D.LL0) : ↥D.LL0) : D.what₂.LL) := h
      simp at this
    · by_contra hn
      rw [not_or] at hn
      have ha : D.what₂.places.val w ((a : ↥D.LL0) : D.what₂.LL) = 0 :=
        le_antisymm (not_lt.1 hn.1) (val_int_nonneg w (isIntegral_coe a))
      have hb : D.what₂.places.val w ((b : ↥D.LL0) : D.what₂.LL) = 0 :=
        le_antisymm (not_lt.1 hn.2) (val_int_nonneg w (isIntegral_coe b))
      have h' : 0 < D.what₂.places.val w (((a * b : 𝓞 ↥D.LL0) : ↥D.LL0) : D.what₂.LL) := h
      have := (D.what₂.places.val w).map_mul ((a : ↥D.LL0) : D.what₂.LL) ((b : ↥D.LL0) : D.what₂.LL)
      rw [ha, hb] at this
      simp [this] at h'
  ne_bot := by
    intro h
    have h1 : ((D.what₂.places.resChar w : ℕ) : 𝓞 ↥D.LL0) ∈ (⊥ : Ideal (𝓞 ↥D.LL0)) := by
      rw [← h]
      show 0 < D.what₂.places.val w ((((D.what₂.places.resChar w : ℕ) : 𝓞 ↥D.LL0) : ↥D.LL0) : D.what₂.LL)
      have := D.what₂.places.val_resChar w
      simp only [map_natCast, RingOfIntegers.coe_eq_algebraMap, SubringClass.coe_natCast]
      rw [this]
      exact_mod_cast D.what₂.places.ramIdx_pos w
    rw [Ideal.mem_bot] at h1
    exact (D.what₂.places.resChar_prime w).ne_zero (by exact_mod_cast h1)

theorem mem_below (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0) :
    x ∈ (below w).asIdeal ↔ 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) := Iff.rfl

def AtPlace (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  ∀ w, Twisted D w → LiesUnder D (t w).1 w ∨ LiesUnder D (t w).1 (D.what₂.places.conj w)

theorem isUnit_of_toOe (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w))
    (h : IsUnit (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
      (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
        (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)))) : IsUnit y := by
  haveI := c.Oe_loc w
  have h1 := (isUnit_map_iff _ _).1 h
  clear h
  generalize c.k' w = k at h1
  generalize c.twI w = i at y k h1
  haveI := D.ntw.Ok_fin i k
  haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i _)
  have h2 := (isUnit_map_iff (algebraMap (D.ntw.O i) (D.ntw.Ok i k)) _).1 h1
  by_contra hy
  have hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) h0
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 i), map_eq_zero] at this
    exact (D.ntw.lPrime i).out.ne_zero (by exact_mod_cast this)
  have hP : ((IsLocalRing.maximalIdeal (D.ntw.O i)).comap (algebraMap (D.ntw.O0 i) (D.ntw.O i))).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => hl ?_
    rw [← Ideal.mem_bot, ← h0, Ideal.mem_comap, map_natCast]
    exact D.ntw.O_l i
  have hm : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := hy
  rw [← IsLocalRing.eq_maximalIdeal hP, Ideal.mem_comap] at hm
  exact hm h2

theorem pos_iff_not_isUnit (c : NChoice D) (w : D.what₂.places.Pl) (x : D.what₂.LL) (z : c.Oe w)
    (h : c.embW w x = algebraMap (c.Oe w) (FractionRing (c.Oe w)) z) :
    0 < D.what₂.places.val w x ↔ ¬ IsUnit z := by
  rcases eq_or_ne x 0 with rfl | h0
  · have : z = 0 := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (by rw [← h, map_zero, map_zero])
    simp [this]
  have hx : 0 ≤ D.what₂.places.val w x := (c.embW_w w x).2 ⟨z, h.symm⟩
  have hmul := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ h0, AddValuation.map_one] at hmul
  have e1 : 0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
    rw [D.val_eq w x h0, D.val_eq w _ (inv_ne_zero h0)] at *
    norm_cast at *
    omega
  rw [e1, c.embW_w, not_iff_not]
  have hz : c.embW w x ≠ 0 := by simpa using h0
  constructor
  · rintro ⟨u, hu⟩
    refine IsUnit.of_mul_eq_one u (IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) ?_)
    rw [map_mul, hu, ← h, map_one, ← map_mul, mul_inv_cancel₀ h0, map_one]
  · rintro ⟨u, rfl⟩
    refine ⟨((u⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    rw [map_inv₀, h]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem exists_star (hG : IsGalois ℚ ↥D.LL0) (x : ↥D.LL0) : ∃ x' : ↥D.LL0, (x' : D.what₂.LL) = star (x : D.what₂.LL) := by
  let σ : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  exact ⟨σ.restrictNormal ↥D.LL0 x, σ.restrictNormal_commutes ↥D.LL0 x⟩

theorem liesUnder_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) :
    LiesUnder D (c.twI w) (if c.sd w then w else D.what₂.places.conj w) := by
  intro x
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (c.twI w))
      (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have key : ∀ x' : ↥D.LL0, (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x' =
      D.ntw.emb0 (c.twI w) (x : ↥D.LL0) → (0 < D.what₂.places.val w (x' : D.what₂.LL) ↔ ¬ IsUnit y) := by
    intro x' hx'
    have e := h.embedding_baseField_condition w x' y 1 one_ne_zero (by rw [hx', map_one, mul_one, hy])
    simp only [map_one, mul_one] at e
    rw [pos_iff_not_isUnit c w _ _ e, not_iff_not]
    exact ⟨isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩
  rw [hleft]
  cases hs : c.sd w
  · obtain ⟨x', hx'⟩ := exists_star hG (x : ↥D.LL0)
    rw [if_neg (by simp), D.conj_val, ← hx']
    refine (key x' ?_).symm
    rw [hs, if_neg (by simp)]
    exact D.ntw.restX_coefficientEmbedding_conj _ _ _ (by rw [hx', star_star])
  · rw [if_pos rfl]
    exact (key x (by rw [hs, if_pos rfl])).symm

theorem atPlace_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) : AtPlace (recorded c) := by
  intro w _
  have := liesUnder_of_tie hG h w
  split_ifs at this
  exacts [Or.inl this, Or.inr this]

end GlobalTheory.TwistGoodCompare

end
