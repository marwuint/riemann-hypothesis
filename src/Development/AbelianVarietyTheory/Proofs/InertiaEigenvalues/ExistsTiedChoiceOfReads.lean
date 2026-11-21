import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

variable {D : D7}

def Apart (Q Q' : Finset (PlE D.host)) : Prop :=
  ∀ P ∈ Q, ∀ P' ∈ Q', ∀ p : ℕ, p.Prime → ¬ (P ∈ placesOver D.host.E p ∧ P' ∈ placesOver D.host.E p)

theorem Apart.symm {Q Q' : Finset (PlE D.host)} (h : Apart Q Q') : Apart Q' Q :=
  fun P hP P' hP' p hp hh => h P' hP' P hP p hp hh.symm

open Classical in
theorem goodTw_union {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S} {A B Q : Finset (PlE D.host)} {k : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S (A ∪ B) Q k ψ) :
    IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ ∧ Disjoint Q B := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨⟨⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.1, h2.2.2.1⟩, h3⟩, h4⟩, h2.2.2.2⟩

def Reading.Pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w)
    {Q : Finset (PlE D.host)} (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
    (algebraMap (D.ntw.Ok i k) ρ.Oe ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))

def HasReading (p : TwPack D) (b : Bool) (w : D.what₂.places.Pl) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∃ ρ : Reading p.1 p.2.2.1 b w, ρ.Pulls (BlochKatoReduction.Gen.psiAt b p.2.2.2) ψ₀

theorem psiAt_not {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (x : Γ) :
    BlochKatoReduction.Gen.psiAt (!b) ψ x = (BlochKatoReduction.Gen.psiAt b ψ x)⁻¹ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

theorem pull_inv {L K A B Δ : Type} [Field L] [Field K] [CommRing A] [CommRing B] [Group Δ] [Fintype Δ] (e : L →+* K)
    (m : A →+* B) (m' : B →+* K) (χ : Δ →* Aˣ) (x : Lˣ) (δ : Δ) (h : e (x : L) = m' (m (χ δ : A))) :
    x ^ Fintype.card Δ = 1 ∧ e ((x⁻¹ : Lˣ) : L) = m' (m (((χ δ)⁻¹ : Aˣ) : A)) := by
  constructor
  · apply Units.ext
    apply e.injective
    rw [Units.val_pow_eq_pow_val, map_pow e, h, ← map_pow m', ← map_pow m, ← Units.val_pow_eq_pow_val, ← map_pow χ,
      pow_card_eq_one]
    simp
  · rw [Units.val_inv_eq_inv_val, map_inv₀, h]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem Reading.Pulls.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} {ρ : Reading i k b w}
    {Q : Finset (PlE D.host)} {ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (hρ : ρ.Pulls ψ ψ₀) (h : ∀ x, ψ' x = (ψ x)⁻¹) : (ρ.conj hG).Pulls ψ' ψ₀ := by
  intro g
  have h0 := pull_inv ρ.emb (algebraMap (D.ntw.Ok i k) ρ.Oe) (algebraMap ρ.Oe (FractionRing ρ.Oe)) ψ (ψ₀ g) (D.ntw.art i Q g) (hρ g)
  have h2 := h0.2
  rw [← star_root Fintype.card_pos h0.1, ← h] at h2
  exact h2

theorem HasReading.conj (hG : IsGalois ℚ ↥D.LL0) {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h : HasReading p b w ψ₀) :
    HasReading p (!b) (D.what₂.places.conj w) ψ₀ :=
  let ⟨ρ, hρ⟩ := h
  ⟨ρ.conj hG, hρ.conj hG (psiAt_not b _)⟩

def RankEq (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (w : D.what₂.places.Pl) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) =
    Module.finrank (FractionRing (D.ntw.Ok i k)) (D.nexp.MtV i j b k Q (ψ.comp (D.ntw.art i Q)))

theorem exists_formsIso {Oe : Type} [CommRing Oe] [IsDomain Oe] [IsDiscreteValuationRing Oe] {A : Type} [CommRing A] [IsDomain A] [Algebra A Oe]
    (hinj : Function.Injective (algebraMap A Oe)) {V : Type} [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) (e : D.what₂.LL →+* FractionRing Oe) (μ : D.what₂.Tup) (j : ℕ) (c : Prop)
    (h : c → Module.finrank D.what₂.LL (D.what₂.MtL μ j) = Module.finrank (FractionRing A) V) :
    ∃ f : D.what₂.MtL μ j →ₛₗ[e] FractionRing Oe ⊗[A] V, c →
      (∀ (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) D.what₂.LL (D.what₂.MtL μ j)),
        LinearIndependent (FractionRing Oe) (fun a => f (b a)) ∧
          Submodule.span (FractionRing Oe) (Set.range fun a => f (b a)) = ⊤) ∧
      Submodule.span Oe (f '' {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}) =
        Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V)) := by
  by_cases hj : c
  · obtain ⟨h1, h2, h3⟩ := form_gen (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _)
      (D.what₂.jMt_basis _ j _) _ (D.what₂.MtLat μ j).span_top (D.what₂.MtLat_sub _ j)
    obtain ⟨h4, h5⟩ := baseChange_lattice hinj Λ hfg hspan
    obtain ⟨f, hf⟩ := exists_semilinear e _ h2 h3
      (Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V))) ((h hj).trans h4.symm)
    exact ⟨f, fun _ => ⟨fun b => hf.1 _ b, hf.2⟩⟩
  · exact ⟨0, fun h1 => absurd h1 hj⟩

section ChoiceOf

variable (twI : D.what₂.places.Pl → D.ntw.Tw) (b : D.what₂.places.Pl → Bool) (Q : D.what₂.places.Pl → Finset (PlE D.host))
  (k : D.what₂.places.Pl → ℕ) (ψ : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k w))ˣ)
  (hr : ∀ w, ReadsAt (twI w) (b w) w) (ρ : ∀ w, Reading (twI w) (k w) (b w) w)
  (h : ∀ w, TwistedAt D w → RankEq (twI w) (b w) (Q w) (k w) (ψ w) w)

def choiceOf : NChoice D :=
  let H := fun w j => exists_formsIso (ρ w).inj _
    (D.nexp.MtLat_fg (twI w) j (b w) (k w) (Q w) ((ψ w).comp (D.ntw.art (twI w) (Q w))))
    (D.nexp.MtLat_span _ _ _ _ _ _) (ρ w).emb (D.what₂.muTw w) j (TwistedAt D w ∧ 1 ≤ j ∧ j ≤ D.R.m)
    fun c => h w c.1 j c.2.1 c.2.2
  { twI := twI
    twI_l := fun w => (hr w).l_eq
    sd := b
    Q := Q
    k' := k
    psi' := ψ
    Oe := fun w => (ρ w).Oe
    algOOe := fun w => ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
      (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
    towOe := fun w =>
      letI := ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
        (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Oe_inj := fun w => (ρ w).inj
    Oe_fin := fun w => (ρ w).fin
    Oe_loc := fun w => (ρ w).loc
    embW := fun w => (ρ w).emb
    embW_w := fun w => (ρ w).emb_w
    eMt := fun w j => (H w j).choose
    eMt_basis := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).1
    eMt_lat := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).2 }

end ChoiceOf

theorem readsAt_of_tie {C : NChoice D} (h : NChTie D C) (w : D.what₂.places.Pl) : ReadsAt (C.twI w) (C.sd w) w := by
  intro x
  obtain ⟨φ, hφ⟩ := exists_intMap (sideEmb (C.twI w) (C.sd w))
  haveI := isLocalHom_phiK (C.twI w) (C.k' w)
  haveI := C.Oe_loc w
  have h1 : C.embW w ((x : ↥D.LL0) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w))
      (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    have h2 := h.embedding_baseField_condition w x (φ x) 1 one_ne_zero (by rw [map_one, mul_one, hφ]; rfl)
    simp only [map_one, mul_one] at h2
    exact h2
  have h2 : (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (C.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y = sideEmb (C.twI w) (C.sd w) (x : ↥D.LL0)) ↔
      ¬ IsUnit (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    rw [isUnit_map_iff, isUnit_map_iff]
    exact ⟨fun ⟨y, hy, hy'⟩ => IsFractionRing.injective _ (FractionRing _) (hy'.trans (hφ x).symm) ▸ hy,
      fun hu => ⟨_, hu, hφ x⟩⟩
  rw [h2]
  generalize algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x)) = u at h1
  generalize ((x : ↥D.LL0) : D.what₂.LL) = x' at h1
  by_cases hx : x' = 0
  · subst hx
    rw [map_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h1
    simp [h1]
  have h3 : 0 < D.what₂.places.val w x' ↔ ¬ 0 ≤ D.what₂.places.val w x'⁻¹ := by
    rw [val_pos_iff, val_nonneg_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 (by simpa using hx))]
  have hu : algebraMap (C.Oe w) (FractionRing (C.Oe w)) u ≠ 0 := h1 ▸ (map_ne_zero _).2 hx
  rw [h3, C.embW_w, map_inv₀, h1, not_iff_not]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v⁻¹ : (C.Oe w)ˣ), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩
  · rintro ⟨v, hv⟩
    exact IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing (C.Oe w))
      (by rw [map_mul, hv, mul_inv_cancel₀ hu, map_one]))

theorem ReadsAt.of_pair (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {v w : D.what₂.places.Pl} (h : ReadsAt i b v)
    (h' : OverOnePair D v w) : ∃ b', ReadsAt i b' w := by
  rcases h' with h' | h'
  · exact ⟨b, h.of_overOne h'⟩
  · exact ⟨!b, (h.conj hG).of_overOne h'⟩

abbrev Pass (D : D7) : Type := (∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)) × Finset (TwPack D)

variable {D₀ D₁ : D7} {E₀ : IntegralHeckeForms.XD D₀} {E₁ : IntegralHeckeForms.XD D₁} {E : IntegralHeckeForms.XD D}

end GlobalTheory.TwistChoice

end
