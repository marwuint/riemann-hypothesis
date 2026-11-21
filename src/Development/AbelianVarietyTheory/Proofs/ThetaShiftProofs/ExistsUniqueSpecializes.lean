import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Specialise

open GlobalTheory.Points GlobalTheory.AmpleSpan

section Coords

variable {A : Type} [CommRing A] {X Y : Scheme.{0}} {H : LB X} {ι : Type*} {t : ι → LB.Sec H}
  {x : Sp A ⟶ X} {c : ι → A}

def HasCoords (x : Sp A ⟶ X) (t : ι → LB.Sec H) (c : ι → A) : Prop :=
  ∃ k, ⊤ ≤ x ⁻¹ᵁ H.U k ∧ ∃ u : Aˣ, ∀ l, valR x (H.U k) ((t l).f k) = c l * u

theorem le_preimage_inf (x : Sp A ⟶ X) {U V : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem valR_compat (s : LB.Sec H) (x : Sp A ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j) (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valR x (H.U j) (s.f j) = valR x (H.U j ⊓ H.U k) (H.g j k).val * valR x (H.U k) (s.f k) := by
  have h := le_preimage_inf x hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem HasCoords.chart (h : HasCoords x t c) {j : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j) :
    ∃ u : Aˣ, ∀ l, valR x (H.U j) ((t l).f j) = c l * u := by
  obtain ⟨k, hk, u, hu⟩ := h
  have hg : IsUnit (valR x (H.U j ⊓ H.U k) (H.g j k).val) := by
    rw [valR_eq x _ (le_preimage_inf x hj hk)]
    exact (Units.isUnit _).map _
  refine ⟨hg.unit * u, fun l => ?_⟩
  rw [valR_compat (t l) x hj hk, hu, Units.val_mul, IsUnit.unit_spec, mul_left_comm]

theorem HasCoords.mul_unit (h : HasCoords x t c) {a : A} (ha : IsUnit a) : HasCoords x t fun l => c l * a := by
  obtain ⟨k, hk, u, hu⟩ := h
  obtain ⟨a, rfl⟩ := ha
  exact ⟨k, hk, a⁻¹ * u, fun l => by rw [hu, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]⟩

theorem HasCoords.le_nonzeroLocus (h : HasCoords x t c) {l : ι} (hl : IsUnit (c l)) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t l) := by
  obtain ⟨k, hk, u, hu⟩ := h
  refine le_preimage_mono x (le_iSup (fun k => X.basicOpen ((t l).f k)) k) ?_
  rw [le_preimage_basicOpen_iff x hk, hu]
  exact hl.mul u.isUnit

theorem valR_isRatio {s s₀ : LB.Sec H} {ρ : Γ(X, nonzeroLocus s₀)} (hρ : IsRatio s s₀ ρ) (x : Sp A ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s₀) {k : H.ι} (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valR x (H.U k) (s.f k) = valR x (nonzeroLocus s₀) ρ * valR x (H.U k) (s₀.f k) := by
  have h := le_preimage_inf x hx hk
  have e := congrArg (valR x (nonzeroLocus s₀ ⊓ H.U k)) (hρ k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h, valR_res x _ h] at e

theorem HasCoords.valR_ratio (h : HasCoords x t c) {l m : ι} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t m))
    {ρ : Γ(X, nonzeroLocus (t m))} (hρ : IsRatio (t l) (t m) ρ) : valR x (nonzeroLocus (t m)) ρ * c m = c l := by
  obtain ⟨k, hk, u, hu⟩ := h
  have e := valR_isRatio hρ x hx hk
  rw [hu, hu, ← mul_assoc] at e
  exact (u.mul_left_inj.1 e).symm

theorem exists_chart_isUnit [IsLocalRing A] {s : LB.Sec H} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s) :
    ∃ k, ⊤ ≤ x ⁻¹ᵁ H.U k ∧ IsUnit (valR x (H.U k) (s.f k)) := by
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ((le_preimage_iff x _).1 hx)
  have hk' := (le_preimage_iff x _).2 hk
  have hU := le_preimage_mono x (X.basicOpen_le _) hk'
  exact ⟨k, hU, (le_preimage_basicOpen_iff x hU _).1 hk'⟩

theorem HasCoords.le_nonzeroLocus_iff [IsLocalRing A] (h : HasCoords x t c) (l : ι) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t l) ↔ IsUnit (c l) := by
  refine ⟨fun hx => ?_, h.le_nonzeroLocus⟩
  obtain ⟨k, hk, hu⟩ := exists_chart_isUnit hx
  obtain ⟨u, e⟩ := h.chart hk
  rw [e] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem HasCoords.exists_isUnit [IsLocalRing A] (h : HasCoords x t c) (hcov : ⨆ l, nonzeroLocus (t l) = ⊤) :
    ∃ l, IsUnit (c l) := by
  obtain ⟨l, hl⟩ := exists_le_preimage_of_iSup_eq_top x hcov
  exact ⟨l, (h.le_nonzeroLocus_iff l).1 hl⟩

theorem hasCoords_ratio [IsLocalRing A] {m : ι} (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (t m))
    {ρ : ι → Γ(X, nonzeroLocus (t m))} (hρ : ∀ l, IsRatio (t l) (t m) (ρ l)) :
    HasCoords x t fun l => valR x (nonzeroLocus (t m)) (ρ l) := by
  obtain ⟨k, hk, hu⟩ := exists_chart_isUnit hx
  exact ⟨k, hk, hu.unit, fun l => valR_isRatio (hρ l) x hx hk⟩

theorem valR_eval₂Hom (f : X ⟶ Y) (x : Sp A ⟶ X) {U : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ U) (ρ : ι → Γ(X, U))
    (q : MvPolynomial ι Γ(Y, ⊤)) :
    valR x U (MvPolynomial.eval₂Hom (f.appLE ⊤ U le_top).hom ρ q) =
      MvPolynomial.eval₂Hom (valMap (x ≫ f) ⊤ (le_preimage_top _)).hom (fun l => valR x U (ρ l)) q := by
  rw [valR_eq x U hx, MvPolynomial.map_eval₂Hom, ← appLE_valMap x f (U := ⊤) le_top hx]
  simp only [valR_eq x U hx]
  rfl

end Coords

section Embedded

variable {A : Type} [CommRing A] {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {ι : Type} {t : ι → LB.Sec H}

theorem HasCoords.ext (ht : EmbedsBy f t) {x x' : Sp A ⟶ X} (hf : x ≫ f = x' ≫ f) {c : ι → A}
    (h : HasCoords x t c) (h' : HasCoords x' t c) {m : ι} (hm : IsUnit (c m)) : x = x' := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus hm
  have hx' := h'.le_nonzeroLocus hm
  refine ext_of_valR hD hx hx' fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  rw [valR_eval₂Hom f x hx, valR_eval₂Hom f x' hx']
  have e : (fun l => valR x _ (ρ l)) = fun l => valR x' _ (ρ l) := funext fun l =>
    hm.mul_right_cancel ((h.valR_ratio hx (hρ l)).trans (h'.valR_ratio hx' (hρ l)).symm)
  rw [e]
  simp only [hf]

theorem HasCoords.ext_of_isLocalRing [IsLocalRing A] (ht : EmbedsBy f t) {x x' : Sp A ⟶ X} (hf : x ≫ f = x' ≫ f)
    {c : ι → A} (h : HasCoords x t c) (h' : HasCoords x' t c) : x = x' := by
  obtain ⟨m, hm⟩ := h.exists_isUnit ht.1
  exact h.ext ht hf h' hm

variable {K : Type} [Field K] {j : A →+* K}

end Embedded

section Rings

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K}

def awayRing (i : R →+* K) (r : R) : Subring K := Subring.closure (Set.range i ∪ {(i r)⁻¹})

def toAway (i : R →+* K) (r : R) : R →+* awayRing i r :=
  i.codRestrict _ fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩)

@[simp] theorem coe_toAway (r a : R) : (toAway i r a : K) = i a := rfl

theorem isUnit_toAway {r : R} (hr : i r ≠ 0) : IsUnit (toAway i r r) :=
  IsUnit.of_mul_eq_one ⟨_, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext (mul_inv_cancel₀ hr))

theorem mem_awayRing {r : R} (hr : i r ≠ 0) {z : K} : z ∈ awayRing i r ↔ ∃ (n : ℕ) (a : R), z * i r ^ n = i a := by
  constructor
  · intro hz
    induction hz using Subring.closure_induction with
    | mem z hz =>
      rcases hz with ⟨a, rfl⟩ | rfl
      · exact ⟨0, a, by simp⟩
      · exact ⟨1, 1, by simp [hr]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨m, a, ha⟩ := hz
      obtain ⟨n, b, hb⟩ := hw
      exact ⟨m + n, a * r ^ n + b * r ^ m, by simp only [map_add, map_mul, map_pow, ← ha, ← hb]; ring⟩
    | neg z _ hz =>
      obtain ⟨m, a, ha⟩ := hz
      exact ⟨m, -a, by rw [map_neg, ← ha, neg_mul]⟩
    | mul z w _ _ hz hw =>
      obtain ⟨m, a, ha⟩ := hz
      obtain ⟨n, b, hb⟩ := hw
      exact ⟨m + n, a * b, by rw [map_mul, ← ha, ← hb]; ring⟩
  · rintro ⟨n, a, h⟩
    have : z = i a * (i r)⁻¹ ^ n := by rw [← h, mul_assoc, ← mul_pow, mul_inv_cancel₀ hr, one_pow, mul_one]
    rw [this]
    have h₁ : (i r)⁻¹ ∈ awayRing i r := Subring.subset_closure (Or.inr rfl)
    exact mul_mem (toAway i r a).2 (pow_mem h₁ n)

theorem isLocalization_awayRing (hi : Function.Injective i) {r : R} (hr : i r ≠ 0) :
    letI := (toAway i r).toAlgebra
    IsLocalization.Away r (awayRing i r) := by
  letI := (toAway i r).toAlgebra
  refine IsLocalization.Away.mk _ (isUnit_toAway hr) (fun z => ?_) fun a b h => ?_
  · obtain ⟨n, a, h⟩ := (mem_awayRing hr).1 z.2
    exact ⟨n, a, Subtype.ext h⟩
  · exact ⟨0, congrArg _ (hi (congrArg Subtype.val h))⟩

theorem ne_zero_of_ev (hi : Function.Injective i) {ev : R →+* C} {r : R} (hr : ev r ≠ 0) : i r ≠ 0 :=
  fun h => hr (by rw [hi (h.trans (map_zero i).symm), map_zero])

def awayLift (hi : Function.Injective i) {r : R} (hr : i r ≠ 0) {T : Type} [CommRing T] (g : R →+* T)
    (hg : IsUnit (g r)) : awayRing i r →+* T :=
  letI := (toAway i r).toAlgebra
  haveI := isLocalization_awayRing hi hr
  IsLocalization.Away.lift r hg

@[simp] theorem awayLift_toAway (hi : Function.Injective i) {r : R} (hr : i r ≠ 0) {T : Type} [CommRing T]
    (g : R →+* T) (hg : IsUnit (g r)) (a : R) : awayLift hi hr g hg (toAway i r a) = g a :=
  letI := (toAway i r).toAlgebra
  haveI := isLocalization_awayRing hi hr
  IsLocalization.Away.lift_eq r hg a

def awayEv (hi : Function.Injective i) (ev : R →+* C) {r : R} (hr : ev r ≠ 0) : awayRing i r →+* C :=
  awayLift hi (ne_zero_of_ev hi hr) ev hr.isUnit

@[simp] theorem awayEv_toAway (hi : Function.Injective i) (ev : R →+* C) {r : R} (hr : ev r ≠ 0) (a : R) :
    awayEv hi ev hr (toAway i r a) = ev a := awayLift_toAway _ _ _ _ _

instance ker_isPrime (ev : R →+* C) : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev

abbrev LocAt (ev : R →+* C) : Type := Localization.AtPrime (RingHom.ker ev)

def LocAt.eval (ev : R →+* C) : LocAt ev →+* C :=
  IsLocalization.lift (M := (RingHom.ker ev).primeCompl) (g := ev) fun s => IsUnit.mk0 _ s.2

def LocAt.emb (hi : Function.Injective i) (ev : R →+* C) : LocAt ev →+* K :=
  IsLocalization.lift (M := (RingHom.ker ev).primeCompl) (g := i) fun s => IsUnit.mk0 _ (ne_zero_of_ev hi s.2)

@[simp] theorem LocAt.eval_algebraMap (ev : R →+* C) (a : R) : LocAt.eval ev (algebraMap R _ a) = ev a :=
  IsLocalization.lift_eq _ a

@[simp] theorem LocAt.emb_algebraMap (hi : Function.Injective i) (ev : R →+* C) (a : R) :
    LocAt.emb hi ev (algebraMap R _ a) = i a := IsLocalization.lift_eq _ a

theorem LocAt.isUnit_algebraMap {ev : R →+* C} {s : R} (hs : ev s ≠ 0) : IsUnit (algebraMap R (LocAt ev) s) :=
  IsLocalization.map_units (M := (RingHom.ker ev).primeCompl) _ ⟨s, hs⟩

theorem LocAt.surj {ev : R →+* C} (z : LocAt ev) :
    ∃ a s : R, ev s ≠ 0 ∧ z * algebraMap R _ s = algebraMap R _ a := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (RingHom.ker ev).primeCompl z
  exact ⟨a, s, s.2, h⟩

instance LocAt.isLocalHom_eval (ev : R →+* C) : IsLocalHom (LocAt.eval ev) :=
  ⟨fun z hz => by
    obtain ⟨a, s, hs, h⟩ := LocAt.surj z
    have e := congrArg (LocAt.eval ev) h
    rw [map_mul, LocAt.eval_algebraMap, LocAt.eval_algebraMap] at e
    exact isUnit_of_mul_isUnit_left (h ▸ LocAt.isUnit_algebraMap (e ▸ mul_ne_zero hz.ne_zero hs))⟩

end Rings

theorem spMap_spMap {A B D : Type} [CommRing A] [CommRing B] [CommRing D] {g : A →+* B} {g' : B →+* D}
    {g'' : A →+* D} (h : ∀ a, g' (g a) = g'' a) {X : Scheme.{0}} (z : Sp A ⟶ X) :
    spMap g' ≫ spMap g ≫ z = spMap g'' ≫ z := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, show g'.comp g = g'' from RingHom.ext h]

section Relation

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {X S : Scheme.{0}}

def Specializes (hi : Function.Injective i) (ev : R →+* C) (p : X ⟶ S) (b : Sp R ⟶ S) (x : Sp K ⟶ X)
    (y : Sp C ⟶ X) : Prop :=
  ∃ ξ : Sp (LocAt ev) ⟶ X, ξ ≫ p = spMap (algebraMap R _) ≫ b ∧ spMap (LocAt.emb hi ev) ≫ ξ = x ∧
    spMap (LocAt.eval ev) ≫ ξ = y

variable {hi : Function.Injective i} {ev : R →+* C} {p : X ⟶ S} {b : Sp R ⟶ S} {x : Sp K ⟶ X} {y : Sp C ⟶ X}

theorem Specializes.over_left (h : Specializes hi ev p b x y) : x ≫ p = spMap i ≫ b := by
  obtain ⟨ξ, hp, rfl, -⟩ := h
  rw [Category.assoc, hp, spMap_spMap (LocAt.emb_algebraMap hi ev)]

theorem Specializes.over_right (h : Specializes hi ev p b x y) : y ≫ p = spMap ev ≫ b := by
  obtain ⟨ξ, hp, -, rfl⟩ := h
  rw [Category.assoc, hp, spMap_spMap (LocAt.eval_algebraMap ev)]

theorem Specializes.map (h : Specializes hi ev p b x y) {X' S' : Scheme.{0}} {p' : X' ⟶ S'} (f : X ⟶ X')
    (g : S ⟶ S') (w : f ≫ p' = p ≫ g) : Specializes hi ev p' (b ≫ g) (x ≫ f) (y ≫ f) := by
  obtain ⟨ξ, hp, rfl, rfl⟩ := h
  exact ⟨ξ ≫ f, by rw [Category.assoc, w, ← Category.assoc, hp, Category.assoc], by rw [Category.assoc],
    by rw [Category.assoc]⟩

theorem Specializes.comp (h : Specializes hi ev p b x y) {X' : Scheme.{0}} {p' : X' ⟶ S} (f : X ⟶ X')
    (w : f ≫ p' = p) : Specializes hi ev p' b (x ≫ f) (y ≫ f) := by
  simpa only [Category.comp_id] using h.map f (𝟙 S) (w.trans (Category.comp_id p).symm)

theorem Specializes.of_isPullback {X' S' : Scheme.{0}} {p' : X' ⟶ S'} {f : X ⟶ X'} {g : S ⟶ S'}
    (sq : IsPullback f p p' g) (hx : x ≫ p = spMap i ≫ b) (hy : y ≫ p = spMap ev ≫ b)
    (h : Specializes hi ev p' (b ≫ g) (x ≫ f) (y ≫ f)) : Specializes hi ev p b x y := by
  obtain ⟨ξ, hp, h₁, h₂⟩ := h
  refine ⟨sq.lift ξ (spMap (algebraMap R _) ≫ b) (by rw [hp, Category.assoc]), sq.lift_snd _ _ _,
    sq.hom_ext ?_ ?_, sq.hom_ext ?_ ?_⟩
  · rw [Category.assoc, sq.lift_fst, h₁]
  · rw [Category.assoc, sq.lift_snd, hx, spMap_spMap (LocAt.emb_algebraMap hi ev)]
  · rw [Category.assoc, sq.lift_fst, h₂]
  · rw [Category.assoc, sq.lift_snd, hy, spMap_spMap (LocAt.eval_algebraMap ev)]

end Relation

section Group

open MonObj

variable {R K C : Type} [CommRing R] [Field K] [Field C] {i : R →+* K} {S : Scheme.{0}} {A : Over S}
  {hi : Function.Injective i} {ev : R →+* C} {b : Sp R ⟶ S} {sK : Sp K ⟶ S} {sC : Sp C ⟶ S}

theorem specializes_iff_over (hK : spMap i ≫ b = sK) (hC : spMap ev ≫ b = sC) (x : Over.mk sK ⟶ A)
    (y : Over.mk sC ⟶ A) : Specializes hi ev A.hom b x.left y.left ↔
      ∃ ξ : Over.mk (spMap (algebraMap R (LocAt ev)) ≫ b) ⟶ A,
        (Over.homMk (spMap (LocAt.emb hi ev)) ((spMap_spMap (LocAt.emb_algebraMap hi ev) b).trans hK) :
          Over.mk sK ⟶ Over.mk (spMap (algebraMap R (LocAt ev)) ≫ b)) ≫ ξ = x ∧
        (Over.homMk (spMap (LocAt.eval ev)) ((spMap_spMap (LocAt.eval_algebraMap ev) b).trans hC) :
          Over.mk sC ⟶ Over.mk (spMap (algebraMap R (LocAt ev)) ≫ b)) ≫ ξ = y :=
  ⟨fun ⟨ξ, h, hx, hy⟩ => ⟨Over.homMk ξ h, Over.OverMorphism.ext hx, Over.OverMorphism.ext hy⟩,
    fun ⟨ξ, hx, hy⟩ => ⟨ξ.left, Over.w ξ, congrArg CommaMorphism.left hx, congrArg CommaMorphism.left hy⟩⟩

theorem Specializes.base_left {x : Over.mk sK ⟶ A} {y : Sp C ⟶ A.left} (h : Specializes hi ev A.hom b x.left y) :
    spMap i ≫ b = sK := h.over_left.symm.trans (Over.w x)

theorem Specializes.base_right {x : Sp K ⟶ A.left} {y : Over.mk sC ⟶ A} (h : Specializes hi ev A.hom b x y.left) :
    spMap ev ≫ b = sC := h.over_right.symm.trans (Over.w y)

theorem Specializes.mul [MonObj A] {x x' : Over.mk sK ⟶ A} {y y' : Over.mk sC ⟶ A}
    (h : Specializes hi ev A.hom b x.left y.left) (h' : Specializes hi ev A.hom b x'.left y'.left) :
    Specializes hi ev A.hom b (x * x').left (y * y').left := by
  have hK := h.base_left
  have hC := h.base_right
  obtain ⟨ξ, rfl, rfl⟩ := (specializes_iff_over hK hC x y).1 h
  obtain ⟨ξ', rfl, rfl⟩ := (specializes_iff_over hK hC x' y').1 h'
  exact (specializes_iff_over hK hC _ _).2 ⟨ξ * ξ', MonObj.comp_mul _ _ _, MonObj.comp_mul _ _ _⟩

theorem Specializes.inv [GrpObj A] {x : Over.mk sK ⟶ A} {y : Over.mk sC ⟶ A}
    (h : Specializes hi ev A.hom b x.left y.left) : Specializes hi ev A.hom b (x⁻¹).left (y⁻¹).left := by
  have hK := h.base_left
  have hC := h.base_right
  obtain ⟨ξ, rfl, rfl⟩ := (specializes_iff_over hK hC x y).1 h
  exact (specializes_iff_over hK hC _ _).2 ⟨ξ⁻¹, GrpObj.comp_inv _ _, GrpObj.comp_inv _ _⟩

end Group

end GlobalTheory.Specialise
