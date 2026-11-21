import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbeddingClosedIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsomComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinExtConjIntOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.RowRhoInt

theorem isRepOf_conj (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (P : GL (Fin a) (Qbar l)) (hρ : ∀ g, ρ' g = P⁻¹ * ρ g * P)
    (h : IsRepOf D l ι π s ρ) : IsRepOf D l ι π s ρ' := by
  have hcoe : ∀ g, ((ρ' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) =
      ((P⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
        ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) * (P : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g; rw [hρ g, Units.val_mul, Units.val_mul]
  refine ⟨?_, Formalism.MainNotions.SumRepresentations.isSSRep_conj ρ ρ' P hρ h.2.1, ?_⟩
  · simp only [hcoe]
    exact (continuous_const.matrix_mul h.1).matrix_mul continuous_const
  · filter_upwards [h.2.2] with w hw B σ hB hσ
    rw [hcoe, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    exact hw B σ hB hσ

theorem isRepOf_map (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (τ : Qbar l ≃ₐ[ℚ_[l]] Qbar l)
    (h : IsRepOf D l (τ.toRingEquiv.trans ι) π s ρ) : IsRepOf D l ι π s (mapRep τ.toRingEquiv.toRingHom ρ) := by
  have hcoe : ∀ g, ((mapRep τ.toRingEquiv.toRingHom ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) =
      ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).map τ.toRingEquiv.toRingHom := fun _ => rfl
  have hnorm : ∀ x : Qbar l, ‖τ x‖ = ‖x‖ := fun x => (spectralNorm_eq_of_equiv τ x).symm
  have hcont : Continuous (τ : Qbar l → Qbar l) := (AddMonoidHomClass.isometry_of_norm τ hnorm).continuous
  refine ⟨?_, GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ _ _ ρ h.2.1, ?_⟩
  · simp only [hcoe]
    exact h.1.matrix_map hcont
  · filter_upwards [h.2.2] with w hw B σ hB hσ
    rw [hcoe, Matrix.charpoly_map, Polynomial.map_map, ← hw B σ hB hσ]
    congr 1

theorem isRepOf_of_read (D : D7) (l : ℕ) [Fact l.Prime] (ι₀ ι₁ : Qbar l ≃+* ℂ) (j : ↥D.LL0 →+* Qbar l)
    (h0 : ∀ x, ι₀ (j x) = embLL0 D x) (h1 : ∀ x, ι₁ (j x) = embLL0 D x) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (h : IsRepOf D l ι₀ π s ρ)
    (hp : ∀ᶠ w in Filter.cofinite, ∃ p : Polynomial ↥D.LL0,
      p.map (embLL0 D) = galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) :
    IsRepOf D l ι₁ π s ρ := by
  have e0 : ι₀.toRingHom.comp j = embLL0 D := RingHom.ext h0
  have e1 : ι₁.toRingHom.comp j = embLL0 D := RingHom.ext h1
  refine ⟨h.1, h.2.1, ?_⟩
  filter_upwards [h.2.2, hp] with w hw hpw B σ hB hσ
  obtain ⟨p, hp⟩ := hpw
  have e := hw B σ hB hσ
  have hc : ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = p.map j := by
    apply Polynomial.map_injective ι₀.toRingHom ι₀.injective
    rw [e, Polynomial.map_map, e0, hp]
  rw [hc, Polynomial.map_map, e1, hp]

theorem isRepOf_of_split (D : D7) (hC : GlobalTheory.RowTie.ChebSplit D.nd) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (π π' : D.naut.CG a) (s : ℝ) (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (h : IsRepOf D l ι π s ρ) (h' : IsRepOf D l ι π' s ρ')
    (hs : ∀ w, IsSplitPl D.host w → D.naut.locG π w = D.naut.locG π' w) : IsRepOf D l ι π' s ρ := by
  obtain ⟨c₁, s₁, f₁⟩ := h
  obtain ⟨c₂, s₂, f₂⟩ := h'
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ ρ' c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hsp, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg, hs w hsp])
  refine ⟨c₁, s₁, ?_⟩
  filter_upwards [f₂] with w hw B σ hB hσ
  rw [hcp σ]
  exact hw B σ hB hσ

theorem subtype_mapMatrix_injective {K : Type} [CommRing K] (S : Subring K) {a : ℕ} :
    Function.Injective (S.subtype.mapMatrix : Matrix (Fin a) (Fin a) S →+* Matrix (Fin a) (Fin a) K) :=
  fun M N h => Matrix.ext fun i k => Subtype.ext (congrFun (congrFun h i) k)

def restrictRep {K : Type} [CommRing K] (S : Subring K) {Γ : Type} [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) K)
    (hS : ∀ g i k, ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) i k ∈ S) : Γ →* GL (Fin a) S where
  toFun g := ⟨Matrix.of fun i k => ⟨_, hS g i k⟩, Matrix.of fun i k => ⟨_, hS g⁻¹ i k⟩, by
      apply subtype_mapMatrix_injective S
      rw [map_mul, map_one]
      change ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) * ((ρ g⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) = 1
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one], by
      apply subtype_mapMatrix_injective S
      rw [map_mul, map_one]
      change ((ρ g⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]⟩
  map_one' := by
    ext i k
    change ((ρ 1 : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) i k = (1 : Matrix (Fin a) (Fin a) S) i k
    rw [map_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' g h := by
    ext i k
    change ((ρ (g * h) : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) i k =
      ((Matrix.of fun i k => (⟨_, hS g i k⟩ : S)) * Matrix.of fun i k => (⟨_, hS h i k⟩ : S)) i k
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply]
    simp

theorem intOf_mono {l : ℕ} [Fact l.Prime] {K K' : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : K ≤ K') :
    Formalism.L2.TwC.intOf l K ≤ Formalism.L2.TwC.intOf l K' := fun _ hx => ⟨h hx.1, hx.2⟩

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

theorem twistEx : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE),
    GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π →
      ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l),
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := _root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw

theorem conjIntegral : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)),
    Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) →
    ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k,
      ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := _root_.GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

theorem core (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : SideA D cf jE) (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
    (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT)
    (hσ : ∃ k, 1 ≤ k ∧ k ≤ D.R.m ∧ D.what₂.isot k σ ≠ ⊥) (hg : D.nd.goodRow σ) :
    ∃ (L : Loc.FinExt l) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l)),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
      (∀ g i k, ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈
        Formalism.L2.TwC.intOf l L.1) ∧
      ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
          IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  obtain ⟨k, hk1, hk2, hk⟩ := hσ
  obtain ⟨π₀, hc₀, hr₀, hl₀, hp₀⟩ := hR k hk1 hk2 σ hk hg
  obtain ⟨ι₀, hι₀⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq l ↥D.LL0 j (embLL0 D)
  have h0 : ∀ x, ι₀ (j x) = embLL0 D x := fun x => RingHom.congr_fun hι₀ x
  obtain ⟨ρG, hρG⟩ := twistEx hA D cf jE A hG l ι₀ π₀ hc₀ hr₀
  obtain ⟨L, P, hP⟩ := conjIntegral l (G D.host.E D.nd.Om) D.R.r ρG hρG.1
  let ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) := (MulAut.conj P⁻¹).toMonoidHom.comp ρG
  have hρ : ∀ g, ρ g = P⁻¹ * ρG g * P := fun g => by simp [ρ, MulAut.conj_apply]
  have hρ0 : IsRepOf D l ι₀ (D.naut.tw π₀ D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ :=
    isRepOf_conj D l ι₀ _ _ ρG ρ P hρ hρG
  refine ⟨L, ρ, hρ0.1, fun g i k => by rw [hρ]; exact hP g i k, fun π hc hr hl ι hι => ?_⟩
  have h1 := isRepOf_of_read D l ι₀ ι j h0 hι _ _ ρ hρ0 hp₀
  obtain ⟨ρ', hρ'⟩ := twistEx hA D cf jE A hG l ι π hc hr
  refine isRepOf_of_split D hC l ι _ _ _ ρ ρ' h1 hρ' (fun w hw => ?_)
  rw [D.naut.locG_tw, D.naut.locG_tw, hl₀ w hw, hl w hw]

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

section Pick

variable (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE)
  (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)

def GoodOcc (σ : D.what₂.FT) : Prop :=
  (∃ k, 1 ≤ k ∧ k ≤ D.R.m ∧ D.what₂.isot k σ ≠ ⊥) ∧ D.nd.goodRow σ

open Classical in

def pickL (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) : Loc.FinExt l :=
  if h : GoodOcc D σ then (core hA D cf jE A hG hR hC l j σ h.1 h.2).choose else ⟨⊥, inferInstance⟩

def starRestrictSubfield (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) : ↥D.LL0 →+* ↥D.LL0 where
  toFun x := ⟨star (x : D.what₂.LL), hstar x⟩
  map_one' := Subtype.ext (star_one _)
  map_mul' x y := Subtype.ext (star_mul' (x : D.what₂.LL) (y : D.what₂.LL))
  map_zero' := Subtype.ext (star_zero _)
  map_add' x y := Subtype.ext (star_add (x : D.what₂.LL) (y : D.what₂.LL))

def jSide (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l)
    (b : Bool) : ↥D.LL0 →+* PadicAlgCl l :=
  if b then j else j.comp (starRestrictSubfield D hstar)

end Pick

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

section HidaSetting

variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}

def kap (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) : FractionRing (T.O0 i) →+* PadicAlgCl (T.l i) :=
  IsFractionRing.lift (g := (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1).subtype.comp (Sp.eO0 i).toRingHom)
    (Subtype.val_injective.comp (Sp.eO0 i).injective)

theorem kap_alg (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (y : T.O0 i) :
    kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) y) = (Sp.eO0 i y : PadicAlgCl (T.l i)) :=
  IsFractionRing.lift_algebraMap _ _

theorem twistFractionFieldToPadicAlgebraicClosure_padicInt (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (z : ℤ_[T.l i]) :
    kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i)) (z : ℚ_[T.l i]) := by
  rw [kap_alg]; exact Sp.ringSpec_baseIntegersEquiv_algebraMap i z

theorem kap_emb0 (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (x : ↥D.LL0) : kap Sp i (T.emb0 i x) = Sp.j0 i x := by
  obtain ⟨y, z, hz, e⟩ := IsFractionRing.div_surjective (A := T.O0 i) (T.emb0 i x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap (T.O0 i) (FractionRing (T.O0 i)) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hz0
  have h1 : T.emb0 i x * algebraMap (T.O0 i) (FractionRing (T.O0 i)) z = algebraMap (T.O0 i) (FractionRing (T.O0 i)) y := by
    rw [← e, div_mul_cancel₀ _ hz1]
  have h2 := (Sp.ringSpec_baseEmbedding_compatible i x y z hz0).mp h1
  have hz2 : ((Sp.eO0 i z : _) : PadicAlgCl (T.l i)) ≠ 0 := by
    intro h; apply hz0; apply (map_eq_zero_iff (Sp.eO0 i) (Sp.eO0 i).injective).1; exact Subtype.ext h
  rw [← e, map_div₀, kap_alg, kap_alg, ← h2, mul_div_cancel_right₀ _ hz2]

end HidaSetting

end GlobalTheory.HeightCounting.RowRhoInt
