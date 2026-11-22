import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.OmegaRank

theorem mem_pow_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
    x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem dual_dvd_iff {O : Type} [CommRing O] (p n : ℕ) (x : DualNumber O) :
    (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
  have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
    rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
  rw [e]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩

theorem isAdicComplete_dualNumber {O : Type} [CommRing O] (p : ℕ)
    [h : IsAdicComplete (Ideal.span {(p : O)}) O] :
    IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) where
  haus' x hx := by
    simp only [SModEq.zero, mem_pow_iff, dual_dvd_iff] at hx
    refine TrivSqZeroExt.ext (h.haus' x.fst fun n => ?_) (h.haus' x.snd fun n => ?_)
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).1
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).2
  prec' f hf := by
    simp only [SModEq.sub_mem, mem_pow_iff, dual_dvd_iff] at hf ⊢
    obtain ⟨a, ha⟩ := h.prec' (fun n => (f n).fst) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).1
    obtain ⟨b, hb⟩ := h.prec' (fun n => (f n).snd) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).2
    simp only [SModEq.sub_mem, mem_pow_iff] at ha hb
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩

theorem exists_param {O : Type} [CommRing O] [IsLocalRing O] (H : Over (Sp O)) [GrpObj H] {n : ℕ}
    (hH : SmoothOfRelativeDimension n H.hom) :
    ∃ e : (Fin n → O) ≃ LieG H, (∀ c d, (e (c + d)).1 = (e c).1 * (e d).1) ∧
      ∀ (a : O) c, (e (a • c)).1 = ptMap (dualScale a) ≫ (e c).1 := by
  obtain ⟨x, hx⟩ := KeyPow.exists_isUnivChart H hH
  refine ⟨⟨fun c => ⟨Chart.tvec (x := x) c, Chart.isTan_tvec hx c⟩, fun w => Chart.tcoord hx w.1 w.2,
    fun c => Chart.tcoord_tvec hx c, fun w => Subtype.ext (Chart.tcoord_spec hx w.1 w.2).symm⟩,
    fun c d => Chart.tvec_add hx c d, fun a c => Chart.tvec_smul hx a c⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem smoothDim_model : SmoothOfRelativeDimension P.A.g P.G.hom := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have := P.semi.smooth
  have := P.semi.geomConnected
  have : ConnectedSpace P.G.left := GeometricallyConnected.connectedSpace P.G.hom P.G.hom.isOpenMap
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected P.G.hom (Classical.arbitrary _)
  have h₁ : SmoothOfRelativeDimension n P.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback P.gen_pull.1 hn
  rwa [← H1.dim_unique _ h₁ P.A.smoothDim (η[P.A.A].left (IsLocalRing.closedPoint C))]

section Lim

variable {R : Type} [CommRing R] [Algebra O R]

variable (p O R) in

abbrev redR (m : ℕ) : R →ₐ[O] R ⧸ Ideal.span {(p : R) ^ m} := Ideal.Quotient.mkₐ O _

omit [Fact p.Prime] in
theorem nilpR (m : ℕ) : IsNilpotent (p : R ⧸ Ideal.span {(p : R) ^ m}) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

omit [Fact p.Prime] in
theorem factor_redR (m : ℕ) : ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (p : R) (Nat.le_succ m)))) ≫ ptMap (redR p O R (m + 1)) = ptMap (redR p O R m) := by
  rw [TangentPow.ptMap_comp_ptMap]
  rfl

def Corr (x : specO O R ⟶ P.Gt) (y : specO O R ⟶ P.G) : Prop :=
  ∀ m, ptMap (redR p O R m) ≫ y = P.cmp _ (nilpR m) (ptMap (redR p O R m) ≫ x)

variable {P}

theorem Corr.mul {x x' : specO O R ⟶ P.Gt} {y y' : specO O R ⟶ P.G} (h : Corr P x y) (h' : Corr P x' y') :
    Corr P (x * x') (y * y') := fun m => by
  rw [MonObj.comp_mul, MonObj.comp_mul, map_mul, h, h']

theorem Corr.one : Corr P (1 : specO O R ⟶ P.Gt) 1 := fun m => by
  rw [MonObj.comp_one, MonObj.comp_one, map_one]

theorem Corr.comp {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R') {x : specO O R ⟶ P.Gt}
    {y : specO O R ⟶ P.G} (h : Corr P x y) : Corr P (ptMap φ ≫ x) (ptMap φ ≫ y) := fun m => by
  let ψ : (R ⧸ Ideal.span {(p : R) ^ m}) →ₐ[O] R' ⧸ Ideal.span {(p : R') ^ m} :=
    Ideal.quotientMapₐ _ φ (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have e : ptMap (redR p O R' m) ≫ ptMap φ = ptMap ψ ≫ ptMap (redR p O R m) := by
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap]
    rfl
  rw [← Category.assoc, ← Category.assoc, e, Category.assoc, Category.assoc, h,
    P.cmp_nat _ _ (nilpR m) (nilpR m)]

variable [IsLocalRing R] (hp : ¬ IsUnit (p : R)) (hc : IsAdicComplete (Ideal.span {(p : R)}) R)
include hp hc

theorem existsUnique_right (x : specO O R ⟶ P.Gt) : ∃! y, Corr P x y :=
  AdicPt.existsUnique_lim O R (p : R) hp hc P.G _
    fun m => by rw [← P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), ← Category.assoc, factor_redR]

theorem existsUnique_left (y : specO O R ⟶ P.G) : ∃! x, Corr P x y := by
  have h := AdicPt.existsUnique_lim O R (p : R) hp hc P.Gt
    (fun m => (P.cmp _ (nilpR m)).symm (ptMap (redR p O R m) ≫ y)) fun m =>
      (P.cmp _ (nilpR m)).injective (by
        rw [P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, ← Category.assoc, factor_redR])
  obtain ⟨x, hx, hu⟩ := h
  refine ⟨x, fun m => by rw [hx, MulEquiv.apply_symm_apply], fun x' hx' => hu x' fun m => ?_⟩
  rw [hx' m, MulEquiv.symm_apply_apply]

end Lim

theorem exists_lieEquiv [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃ e : LieG P.G ≃ LieG P.Gt, (∀ x y z : LieG P.G, z.1 = x.1 * y.1 → (e z).1 = (e x).1 * (e y).1) ∧
      ∀ (a : O) (x z : LieG P.G), z.1 = ptMap (dualScale a) ≫ x.1 →
        (e z).1 = ptMap (dualScale a) ≫ (e x).1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hc := isAdicComplete_dualNumber (O := O) p
  have hl := existsUnique_left (P := P) hp hc
  have hr := existsUnique_right (P := P) hp hc
  let f : LieG P.G → LieG P.Gt := fun y => ⟨(hl y.1).choose,
    (existsUnique_left (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hl y.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [y.2] at h
        exact h) Corr.one⟩
  let g : LieG P.Gt → LieG P.G := fun x => ⟨(hr x.1).choose,
    (existsUnique_right (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hr x.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [x.2] at h
        exact h) Corr.one⟩
  have hf : ∀ y, Corr P (f y).1 y.1 := fun y => (hl y.1).choose_spec.1
  have hg : ∀ x, Corr P x.1 (g x).1 := fun x => (hr x.1).choose_spec.1
  refine ⟨⟨f, g, fun y => Subtype.ext ((hr _).unique (hg _) (hf y)),
    fun x => Subtype.ext ((hl _).unique (hf _) (hg x))⟩, fun x y z h => ?_, fun a x z h => ?_⟩
  · exact (hl _).unique (hf z) (h ▸ (hf x).mul (hf y))
  · exact (hl _).unique (hf z) (h ▸ (hf x).comp (dualScale a))

end GlobalTheory.HTLat.OmegaRank
