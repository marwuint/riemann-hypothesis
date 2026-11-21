import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open TrivSqZeroExt hiding map lift
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Der

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀]

def IsDef (y : FrPt Xo c K) (v : FrPt Xo c (DualNumber K)) : Prop := FrMap (red c K) v y

def der (φ : K₀ →ₐ[c.F] K) (v : FrPt Xo c (DualNumber K)) (s : RulK Xo c K₀) : K :=
  (val ((cst c K).comp φ) v s).snd

def IsShift (N : FIx Dw → K) (v v' : FrPt Xo c (DualNumber K)) : Prop := FrChg (unip K N) (unip₀ K N) v v'

def IsVert (y : FrPt Xo c K) (N : FIx Dw → K) (v : FrPt Xo c (DualNumber K)) : Prop :=
  ∃ y₀, FrMap (cst c K) y y₀ ∧ IsShift N y₀ v

theorem existsUnique_isShift (N : FIx Dw → K) (v : FrPt Xo c (DualNumber K)) : ∃! v', IsShift N v v' :=
  existsUnique_frChg E H Dw l Xo c _ v _ (isUnit_unip₀ N).unit (isUnit_det_unip N)

theorem isShift_zero (v : FrPt Xo c (DualNumber K)) : IsShift (0 : FIx Dw → K) v v := by
  have := (frChg_calculus E H Dw l Xo c _).2.1 v
  unfold IsShift
  convert this using 2 with τ
  · ext i j <;> by_cases h : i = j <;> simp [unip, Matrix.one_apply, h]
  · simp [unip₀]

theorem IsShift.unique {N N' : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsShift N v v')
    (h' : IsShift N' v v') : N = N' := by
  obtain ⟨h1, h2⟩ := (frChg_exists_unique E H Dw l Xo c _ v v').2 _ _ _ _ h h'
  funext k
  rcases k with _ | ⟨σ, i, j⟩
  · simpa [unip₀] using congrArg snd h2
  · simpa [unip] using congrArg (fun g => (g σ i j).snd) h1

theorem IsDef.shift {y : FrPt Xo c K} {N : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v)
    (h' : IsShift N v v') : IsDef y v' := by
  refine (frMap_iff_frChg h' h).2 ?_
  convert (frChg_calculus E H Dw l Xo c _).2.1 y using 2 with τ
  · ext i j; simp [unip]
  · simp [unip₀]

theorem IsDef.exists_isShift {y : FrPt Xo c K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v) (h' : IsDef y v')
    (hx : v'.x = v.x) : ∃ N : FIx Dw → K, IsShift N v v' := by
  obtain ⟨g, a, -, hc⟩ := (frChg_exists_unique E H Dw l Xo c _ v v').1 hx
  obtain ⟨h1, h2⟩ := (frChg_exists_unique E H Dw l Xo c _ y y).2 _ _ _ _ ((frMap_iff_frChg hc h).1 h')
    ((frChg_calculus E H Dw l Xo c _).2.1 y)
  refine ⟨fun k => k.elim (a : DualNumber K).snd fun q => (g q.1 q.2.1 q.2.2).snd, ?_⟩
  unfold IsShift
  convert hc using 1
  · funext τ
    ext i j
    · simpa [unip] using (congrArg (fun g => g τ i j) h1).symm
    · simp [unip]
  · ext
    · simpa [unip₀] using h2.symm
    · simp [unip₀]

theorem isDef_const {y : FrPt Xo c K} {y₀ : FrPt Xo c (DualNumber K)} (h : FrMap (cst c K) y y₀) : IsDef y y₀ :=
  frMap_of_comp h (frMap_id y) fun _ => rfl

theorem IsVert.isDef {y : FrPt Xo c K} {N : FIx Dw → K} {v : FrPt Xo c (DualNumber K)} (h : IsVert y N v) :
    IsDef y v := h.elim fun _ k => (isDef_const k.1).shift k.2

theorem existsUnique_isVert (y : FrPt Xo c K) (N : FIx Dw → K) : ∃! v, IsVert y N v := by
  obtain ⟨y₀, h₀⟩ := exists_frMap (cst c K) y
  obtain ⟨v, hv, hu⟩ := existsUnique_isShift N y₀
  exact ⟨v, ⟨y₀, h₀, hv⟩, fun v' ⟨y₁, h₁, h'⟩ => hu v' (frMap_unique h₁ h₀ ▸ h')⟩

theorem IsVert.unique {y : FrPt Xo c K} {N N' : FIx Dw → K} {v : FrPt Xo c (DualNumber K)} (h : IsVert y N v)
    (h' : IsVert y N' v) : N = N' := by
  obtain ⟨y₀, h₀, h⟩ := h
  obtain ⟨y₁, h₁, h'⟩ := h'
  exact h.unique (frMap_unique h₁ h₀ ▸ h')

theorem exists_isVert_iff {y : FrPt Xo c K} {v : FrPt Xo c (DualNumber K)} :
    (∃ N : FIx Dw → K, IsVert y N v) ↔ IsDef y v ∧ v.x = spMap (cst c K).toRingHom ≫ y.x := by
  refine ⟨fun ⟨N, h⟩ => ⟨h.isDef, h.elim fun _ k => k.2.1.trans k.1.1⟩, fun ⟨h, hx⟩ => ?_⟩
  obtain ⟨y₀, h₀⟩ := exists_frMap (cst c K) y
  obtain ⟨N, hN⟩ := (isDef_const h₀).exists_isShift h (hx.trans h₀.1.symm)
  exact ⟨N, y₀, h₀, hN⟩

def oneAddEps : Multiplicative K →* (DualNumber K)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => inl 1 + inr x.toAdd
      map_one' := by simp
      map_mul' := fun x y => by ext <;> simp [add_comm] }

def diagOf (N : FIx Dw → K) : Ix Dw → K
  | none => N none
  | some q => N (some ⟨q.1, q.2, q.2⟩)

end Der

section Index

def IsHalf (Φ : Finset (E →+* ℂ)) : Prop := ∀ τ, τ ∈ Φ ↔ conjEmb τ ∉ Φ

variable (H) in

def psiSet : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0

variable (H) in

theorem isHalf_psiSet : IsHalf (psiSet H) := fun τ => by
  simp only [psiSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => conj_not_mem ⟨τ, h⟩, fun h => by_contra fun h' => h (conj_mem h')⟩

variable (Dw)

abbrev HIx (Φ : Finset (E →+* ℂ)) : Type := Σ τ : Φ, Fin (Dw.mult (conjEmb τ.1)) × Fin (Dw.mult τ.1)

abbrev VIx : Type := Σ σ : E →+* ℂ, {q : Fin (Dw.mult σ) × Fin (Dw.mult σ) // q.1 < q.2}

abbrev TIx (Φ : Finset (E →+* ℂ)) : Type := HIx Dw Φ ⊕ VIx Dw

def dimFlag : ℕ := Module.finrank ℚ E / 2 * (Dw.p + Dw.q).choose 2

variable {Dw}

def VIx.toF (k : VIx Dw) : FIx Dw := some ⟨k.1, k.2.1⟩

theorem VIx.toF_injective : Function.Injective (VIx.toF (Dw := Dw)) := by
  rintro ⟨σ, q, hq⟩ ⟨σ', q', hq'⟩ e
  obtain ⟨rfl, e⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
  obtain rfl := eq_of_heq e
  rfl

theorem IsHalf.sum_univ {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) (g : (E →+* ℂ) → ℕ) :
    ∑ σ, g σ = ∑ τ ∈ Φ, (g τ + g (conjEmb τ)) := by
  rw [Finset.sum_add_distrib, ← Finset.sum_add_sum_compl Φ]
  congr 1
  refine Finset.sum_bij' (fun σ _ => conjEmb σ) (fun σ _ => conjEmb σ) (fun σ hσ => ?_) (fun σ hσ => ?_)
    (fun σ _ => conjEmb_conjEmb σ) (fun σ _ => conjEmb_conjEmb σ) fun σ _ => by rw [conjEmb_conjEmb]
  · rw [h, conjEmb_conjEmb]; exact Finset.mem_compl.1 hσ
  · exact Finset.mem_compl.2 ((h σ).1 hσ)

theorem IsHalf.card {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) : Φ.card = Module.finrank ℚ E / 2 := by
  have := h.sum_univ fun _ => 1
  simp only [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul] at this
  omega

theorem mult_conj (τ : E →+* ℂ) : (Dw.mult τ = Dw.p ∧ Dw.mult (conjEmb τ) = Dw.q) ∨
    (Dw.mult τ = Dw.q ∧ Dw.mult (conjEmb τ) = Dw.p) := by
  by_cases h : τ (H.rt : E) = H.rt0
  · exact .inl ⟨if_pos h, if_neg (conj_not_mem ⟨τ, h⟩)⟩
  · exact .inr ⟨if_neg h, if_pos (conj_mem h)⟩

theorem card_HIx {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) : Fintype.card (HIx Dw Φ) = Dw.dim := by
  have : ∀ τ : Φ, Dw.mult (conjEmb τ.1) * Dw.mult τ.1 = Dw.p * Dw.q := fun τ => by
    rcases mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
    exact mul_comm _ _
  simp [Fintype.card_sigma, this, h.card, Datum.dim, mul_assoc]

theorem card_VIx : Fintype.card (VIx Dw) = Module.finrank ℚ E / 2 * (Dw.p.choose 2 + Dw.q.choose 2) := by
  have h1 : ∀ n : ℕ, Fintype.card {q : Fin n × Fin n // q.1 < q.2} = n.choose 2 := fun n => by
    rw [Fintype.card_subtype]
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have h2 : ∀ τ, (Dw.mult τ).choose 2 + (Dw.mult (conjEmb τ)).choose 2 = Dw.p.choose 2 + Dw.q.choose 2 := fun τ => by
    rcases mult_conj (Dw := Dw) τ with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
    exact add_comm _ _
  simp only [Fintype.card_sigma, h1]
  rw [(isHalf_psiSet H).sum_univ]
  simp [h2, (isHalf_psiSet H).card]

theorem card_TIx {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) : Fintype.card (TIx Dw Φ) = dimFlag Dw := by
  have : (Dw.p + Dw.q).choose 2 = Dw.p * Dw.q + (Dw.p.choose 2 + Dw.q.choose 2) := by
    induction Dw.q with
    | zero => simp
    | succ n ih => rw [← add_assoc, Nat.choose_succ_succ' (Dw.p + n), ih, Nat.choose_succ_succ' n]; simp; ring
  rw [Fintype.card_sum, card_HIx h, card_VIx, dimFlag, this, Datum.dim]
  ring

variable (Dw)

def kap : Weight Dw := fun _ j =>
  if (j : ℕ) < Dw.p then (Dw.q : ℤ) + 2 * ((j : ℕ) + 1) - Dw.p - 1
  else -(Dw.p : ℤ) + 2 * (((j : ℕ) : ℤ) - Dw.p + 1) - Dw.q - 1

def detTanEx : Ix Dw → ℤ
  | none => 0
  | some k => ((Finset.Iio k.2).card : ℤ) - (Finset.Ioi k.2).card + Dw.mult (conjEmb k.1)

theorem exOf_kap : exOf Dw (kap Dw) 0 = detTanEx Dw := by
  funext k
  rcases k with _ | ⟨σ, i⟩
  · rfl
  show (wtOf Dw (kap Dw) 0).1 (σ, i) = _
  have hi := i.2
  simp only [detTanEx, Fin.card_Iio, Fin.card_Ioi]
  by_cases h : σ (H.rt : E) = H.rt0
  · have a : Dw.mult σ = Dw.p := if_pos h
    have b : Dw.mult (conjEmb σ) = Dw.q := if_neg (conj_not_mem ⟨σ, h⟩)
    have hp : (i : ℕ) < Dw.p := by omega
    rw [wtOf_big _ 0 ⟨σ, h⟩ i hp]
    simp only [kap, hp, if_true]
    omega
  · have a : Dw.mult σ = Dw.q := if_neg h
    have b : Dw.mult (conjEmb σ) = Dw.p := if_pos (conj_mem h)
    have e := wtOf_small (kap Dw) 0 ⟨conjEmb σ, conj_mem h⟩ i (a ▸ hi)
    simp only [conjEmb_conjEmb] at e
    rw [e]
    simp only [kap, add_lt_iff_neg_left, Nat.not_lt_zero, if_false]
    omega

end Index

section KS

open DeRham Cris

def IsKSRow {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A']
    {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (epsRed R) i) (ψ : LinearMap.BilinForm R (HdR A)) {J : Type}
    (hb : J → HdR A) (a : J) (w : epsR R ⟶ A) : Prop :=
  ∃ f ∈ Fil A, (∀ k, ψ f (hb k) = if k = a then 1 else 0) ∧ IsKSValue h f w

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀]

def IsTanX (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X) : Prop :=
  x' ≫ Xo.s = sOf c (DualNumber K) ∧ spMap (red c K).toRingHom ≫ x' = y.x

theorem IsDef.isTanX {y : FrPt Xo c K} {v : FrPt Xo c (DualNumber K)} (h : IsDef y v) : IsTanX y v.x :=
  ⟨v.x_over, h.1.symm⟩

def IsKS (Φ : Finset (E →+* ℂ)) (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X) (M : HIx Dw Φ → K) : Prop :=
  ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (epsRed K) i) (ψ : LinearMap.BilinForm K (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

def KSIso (Φ : Finset (E →+* ℂ)) (y : FrPt Xo c K) : Prop :=
  ∃ X : Sp (TrivSqZeroExt K (HIx Dw Φ → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧
    spMap (fstHom c.F K (HIx Dw Φ → K)).toRingHom ≫ X = y.x ∧
    ∀ x', IsTanX y x' → (∃! M : HIx Dw Φ → K, x' = spMap (dir c M).toRingHom ≫ X) ∧
      ∀ M : HIx Dw Φ → K, IsKS Φ y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X

theorem KSIso.existsUnique {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) {x' : Sp (DualNumber K) ⟶ Xo.X}
    (hx : IsTanX y x') : ∃! M, IsKS Φ y x' M := by
  obtain ⟨X, -, -, h⟩ := h
  simpa only [(h x' hx).2] using (h x' hx).1

theorem KSIso.injective {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) {x' x'' : Sp (DualNumber K) ⟶ Xo.X}
    (hx : IsTanX y x') (hx' : IsTanX y x'') {M : HIx Dw Φ → K} (k : IsKS Φ y x' M) (k' : IsKS Φ y x'' M) :
    x' = x'' := by
  obtain ⟨X, -, -, h⟩ := h
  rw [((h x' hx).2 M).1 k, ((h x'' hx').2 M).1 k']

theorem KSIso.exists_universal {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) :
    ∃ (W : FrPt Xo c (TrivSqZeroExt K (HIx Dw Φ → K))) (z : (HIx Dw Φ → K) → FrPt Xo c (DualNumber K)),
      ∀ M, FrMap (dir c M) W (z M) ∧ IsDef y (z M) ∧ IsKS Φ y (z M).x M := by
  obtain ⟨X, h1, h2, h⟩ := h
  obtain ⟨W, rfl, hW⟩ := exists_lift y X h1 h2
  choose z hz using fun M : HIx Dw Φ → K => exists_frMap (dir c M) W
  have hd : ∀ M, IsDef y (z M) := fun M => frMap_of_comp (hz M) hW fun a => fst_dir (c := c) M a
  exact ⟨W, z, fun M => ⟨hz M, hd M, ((h _ (hd M).isTanX).2 M).2 (hz M).1⟩⟩

def IsTanFrame (Φ : Finset (E →+* ℂ)) (y : FrPt Xo c K) (v : TIx Dw Φ → FrPt Xo c (DualNumber K)) : Prop :=
  (∀ k : HIx Dw Φ, IsDef y (v (.inl k)) ∧ IsKS Φ y (v (.inl k)).x (Pi.single k 1)) ∧
    ∀ k : VIx Dw, IsVert y (Pi.single k.toF (1 : K)) (v (.inr k))

theorem IsTanFrame.isDef {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} {v : TIx Dw Φ → FrPt Xo c (DualNumber K)}
    (h : IsTanFrame Φ y v) : ∀ k, IsDef y (v k)
  | .inl k => (h.1 k).1
  | .inr k => (h.2 k).isDef

theorem KSIso.exists_isTanFrame {Φ : Finset (E →+* ℂ)} {y : FrPt Xo c K} (h : KSIso Φ y) :
    ∃ v, IsTanFrame Φ y v := by
  obtain ⟨W, z, hz⟩ := h.exists_universal
  choose w hw using fun k : VIx Dw => (existsUnique_isVert y (Pi.single k.toF (1 : K))).exists
  exact ⟨Sum.elim (fun k => z (Pi.single k 1)) w, fun k => (hz _).2, hw⟩

theorem existsUnique_isTanFrame_of_isEmpty {Φ : Finset (E →+* ℂ)} [IsEmpty (HIx Dw Φ)] (y : FrPt Xo c K) :
    ∃! v, IsTanFrame Φ y v := by
  choose w hw hu using fun k : VIx Dw => existsUnique_isVert y (Pi.single k.toF (1 : K))
  refine ⟨Sum.elim isEmptyElim w, ⟨isEmptyElim, hw⟩, fun v hv => funext fun k => ?_⟩
  rcases k with k | k
  · exact isEmptyElim k
  · exact hu k _ (hv.2 k)

theorem isEmpty_HIx (Φ : Finset (E →+* ℂ)) (h : Dw.p = 0 ∨ Dw.q = 0) : IsEmpty (HIx Dw Φ) :=
  ⟨fun ⟨τ, a, b⟩ => by
    have ha := a.2
    have hb := b.2
    rcases mult_conj (Dw := Dw) τ.1 with ⟨k, k'⟩ | ⟨k, k'⟩ <;> omega⟩

theorem sum_FIx (g : FIx Dw → K) :
    ∑ k, g k = ∑ k : VIx Dw, g k.toF + ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range VIx.toF), g k := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => k ∈ Set.range VIx.toF)]
  congr 1
  rw [← Finset.sum_image (f := g) fun a _ b _ e => VIx.toF_injective e]
  congr 1
  ext k
  simp

end KS

section Wedge

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀] {ι : Type} [Fintype ι]

def wedge (φ : K₀ →ₐ[c.F] K) (v : ι → FrPt Xo c (DualNumber K)) (s : ι → RulK Xo c K₀) : K :=
  (Matrix.of fun i k => der φ (v k) (s i)).det

theorem wedge_perm (φ : K₀ →ₐ[c.F] K) (v : ι → FrPt Xo c (DualNumber K)) (σ : Equiv.Perm ι)
    (s : ι → RulK Xo c K₀) : wedge φ (v ∘ σ) s = (Equiv.Perm.sign σ : ℤ) * wedge φ v s :=
  Matrix.det_permute' σ (Matrix.of fun i k => der φ (v k) (s i))

variable {Φ : Finset (E →+* ℂ)}

variable (Φ)

def IsWedgeVal (o : ι ≃ TIx Dw Φ) (φ : K₀ →ₐ[c.F] K) (y : FrPt Xo c K) (s : ι → RulK Xo c K₀) (d : K) : Prop :=
  (∀ i, val φ y (s i) = 0) ∧ ∃ v, IsTanFrame Φ y v ∧ d = wedge φ (v ∘ o) s

variable {Φ}

theorem existsUnique_isWedgeVal_of_isEmpty [IsEmpty (HIx Dw Φ)] (o : ι ≃ TIx Dw Φ) (φ : K₀ →ₐ[c.F] K)
    {y : FrPt Xo c K} {s : ι → RulK Xo c K₀} (h0 : ∀ i, val φ y (s i) = 0) : ∃! d, IsWedgeVal Φ o φ y s d := by
  obtain ⟨v, hv, hu⟩ := existsUnique_isTanFrame_of_isEmpty (Φ := Φ) y
  refine ⟨_, ⟨h0, v, hv, rfl⟩, ?_⟩
  rintro _ ⟨-, w, hw, rfl⟩
  rw [hu w hw]

theorem IsWedgeVal.reorder {o : ι ≃ TIx Dw Φ} {φ : K₀ →ₐ[c.F] K} {y : FrPt Xo c K} {s : ι → RulK Xo c K₀} {d : K}
    (h : IsWedgeVal Φ o φ y s d) (o' : ι ≃ TIx Dw Φ) :
    IsWedgeVal Φ o' φ y s ((Equiv.Perm.sign (o'.trans o.symm) : ℤ) * d) := by
  obtain ⟨h0, v, hv, rfl⟩ := h
  refine ⟨h0, v, hv, ?_⟩
  rw [← wedge_perm]
  congr 1
  funext i
  simp

end Wedge

section Norm

variable {T : CDVR} {io : c.F →+* T.Fr} {K₀ : Type} [CommRing K₀] [Algebra c.F K₀] {ι : Type} [Fintype ι]

variable (c) in

abbrev CoefHom (io : c.F →+* T.Fr) (K₀ : Type) [CommRing K₀] [Algebra c.F K₀] : Type :=
  letI := io.toAlgebra
  K₀ →ₐ[c.F] T.Fr

def secOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : RulK Xo c K₀) : EReal :=
  letI := io.toAlgebra
  nval T.V n (val φ y.1 s)

variable (Φ : Finset (E →+* ℂ))

def IsWedgeOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : ι → RulK Xo c K₀) (w : EReal) : Prop :=
  letI := io.toAlgebra
  ∃ (o : ι ≃ TIx Dw Φ) (d : T.Fr), IsWedgeVal Φ o φ y.1 s d ∧ w = nval T.V n d

def wedgeOrd (n : ℕ) (φ : CoefHom c io K₀) (y : IntFr Xo c T io) (s : ι → RulK Xo c K₀) : EReal :=
  if h : ∃! w, IsWedgeOrd Φ n φ y s w then h.choose else ⊥

def normOfOrd (p : ℕ) (w : EReal) : ENNReal := EReal.exp (-(w * (Real.log p : ℝ)))

variable {Φ}

theorem wedgeOrd_ne_bot_iff {n : ℕ} {φ : CoefHom c io K₀} {y : IntFr Xo c T io} {s : ι → RulK Xo c K₀} :
    wedgeOrd Φ n φ y s ≠ ⊥ ↔ ∃! w, IsWedgeOrd Φ n φ y s w := by
  refine ⟨fun h => by_contra fun h' => h (dif_neg h'), fun h => ?_⟩
  obtain ⟨o, d, -, e⟩ := h.choose_spec.1
  rw [wedgeOrd, dif_pos h, e]
  exact nval_ne_bot _ _

theorem wedgeOrd_eq {n : ℕ} {φ : CoefHom c io K₀} {y : IntFr Xo c T io} {s : ι → RulK Xo c K₀}
    (h : wedgeOrd Φ n φ y s ≠ ⊥) {w : EReal} (hw : IsWedgeOrd Φ n φ y s w) : wedgeOrd Φ n φ y s = w := by
  have h' := wedgeOrd_ne_bot_iff.1 h
  rw [wedgeOrd, dif_pos h']
  exact h'.unique h'.choose_spec.1 hw

theorem nval_sign_mul (n : ℕ) (u : ℤˣ) (x : T.Fr) : nval T.V n (((u : ℤ) : T.Fr) * x) = nval T.V n x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · refine nval_mul_unit n (by simp) ?_ x
    simp [vV]

theorem wedgeOrd_eq_of_unique (n : ℕ) {φ : CoefHom c io K₀} {y : IntFr Xo c T io} {s : ι → RulK Xo c K₀}
    {o : ι ≃ TIx Dw Φ} (h : letI := io.toAlgebra; ∃! d, IsWedgeVal Φ o φ y.1 s d) {d : T.Fr}
    (hd : letI := io.toAlgebra; IsWedgeVal Φ o φ y.1 s d) : wedgeOrd Φ n φ y s = nval T.V n d := by
  letI := io.toAlgebra
  refine wedgeOrd_eq (wedgeOrd_ne_bot_iff.2 ⟨_, ⟨o, d, hd, rfl⟩, ?_⟩) ⟨o, d, hd, rfl⟩
  rintro _ ⟨o', d', hd', rfl⟩
  rw [← h.unique (hd'.reorder o) hd, nval_sign_mul]

end Norm

end GlobalTheory.FlagTan
