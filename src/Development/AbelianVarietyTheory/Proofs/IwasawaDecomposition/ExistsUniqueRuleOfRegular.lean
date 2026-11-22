import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

section Cpt

variable (C : FlagCpt Z e)

def Fk : Type := C.Y.Fn

instance : Field (Fk C) := inferInstanceAs (Field C.Y.Fn)

instance : Algebra c.F (Fk C) := RingHom.toAlgebra (constF e C.Y : c.F →+* C.Y.Fn)

def St (y : C.Y.X) : Type := C.Y.X.presheaf.stalk y

instance (y : C.Y.X) : CommRing (St C y) := inferInstanceAs (CommRing (C.Y.X.presheaf.stalk y))

instance (y : C.Y.X) : IsLocalRing (St C y) := inferInstanceAs (IsLocalRing (C.Y.X.presheaf.stalk y))

def pt (y : C.Y.X) : Sp (St C y) ⟶ C.Y.X := stalkPt C.Y y

instance (y : C.Y.X) : Mono (pt C y) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk y))

instance (y : C.Y.X) : Algebra c.F (St C y) := (Spec.preimage (pt C y ≫ C.π ≫ genStr Z)).hom.toAlgebra

theorem pt_str (y : C.Y.X) : pt C y ≫ C.π ≫ genStr Z = spMap (algebraMap c.F (St C y)) := (Spec.map_preimage _).symm

def gpt : Sp (Fk C) ⟶ C.Y.X := genericPt C.Y

def fr0 : FrPt Xo c (Fk C) := C.y0

theorem frame_point_over : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.jQ = gpt C ≫ C.π := C.y0_x

theorem str_of_over {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T} {x : Sp T ⟶ gen Z}
    (h : GlobalTheory.AllWt.ptF z ≫ Z.jQ = x) : x ≫ genStr Z = spMap (algebraMap c.F T) := by
  rw [← h, Category.assoc, Z.jQ_over, ptF_snd]

variable {C} in

def algOf {T : Type} [CommRing T] [Algebra c.F T] {y : C.Y.X} (ψ : St C y →+* T) {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) : St C y →ₐ[c.F] T :=
  { ψ with commutes' := fun a => DFunLike.congr_fun (sp_inj (f := ψ.comp (algebraMap c.F (St C y))) (by
      rw [← sp_comp, ← pt_str, ← Category.assoc, h, hp])) a }

def toFkR (y : C.Y.X) : St C y →+* Fk C := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField

theorem toFkR_pt (y : C.Y.X) : spMap (toFkR C y) ≫ pt C y = gpt C :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

def toFk (y : C.Y.X) : St C y →ₐ[c.F] Fk C :=
  algOf (toFkR C y) (toFkR_pt C y) (by rw [← Category.assoc]; exact str_of_over (frame_point_over C))

theorem toFk_pt (y : C.Y.X) : spMap (toFk C y).toRingHom ≫ pt C y = gpt C := toFkR_pt C y

theorem toFk_injective (y : C.Y.X) : Function.Injective (toFk C y) :=
  IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField

variable {C}

theorem exists_factor {T : Type} [CommRing T] [IsLocalRing T] [Algebra c.F T] (p : Sp T ⟶ C.Y.X)
    (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) :
    ∃ (y : C.Y.X) (ψ : St C y →ₐ[c.F] T), spMap ψ.toRingHom ≫ pt C y = p ∧ p (IsLocalRing.closedPoint T) = y :=
  have h : spMap (R := St C _) (Scheme.stalkClosedPointTo p).hom ≫ pt C _ = p :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p
  ⟨_, algOf _ h hp, h, rfl⟩

theorem specializes_of {T : Type} [CommRing T] {y : C.Y.X} {ψ : St C y →+* T} {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (s : Sp T) : p s ⤳ y := by
  have : p s ∈ Set.range (C.Y.X.fromSpecStalk y) := ⟨spMap ψ s, by rw [← h]; rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem hom_eq {T : Type} [CommRing T] {y : C.Y.X} {ψ ψ' : St C y →+* T} (h : spMap ψ ≫ pt C y = spMap ψ' ≫ pt C y) :
    ψ = ψ' := sp_inj ((cancel_mono _).1 h)

theorem exists_spec {y y' : C.Y.X} (h : y' ⤳ y) : ∃ sp : St C y →ₐ[c.F] St C y',
    spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  have k : spMap (R := St C y) (R' := St C y') (C.Y.X.presheaf.stalkSpecializes h).hom ≫ pt C y = pt C y' :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  refine ⟨algOf _ k (pt_str C y'), k, fun a => ?_⟩
  refine DFunLike.congr_fun (hom_eq (ψ := (toFk C y').toRingHom.comp (algOf _ k (pt_str C y')).toRingHom)
    (ψ' := (toFk C y).toRingHom) ?_) a
  rw [← sp_comp, Category.assoc, toFk_pt]
  exact (congrArg (_ ≫ ·) k).trans (toFk_pt C y')

theorem x_eq_of_over {T : Type} [CommRing T] [Algebra c.F T] {z z' : FrPt Xo c T}
    (h : GlobalTheory.AllWt.ptF z' ≫ Z.jQ = GlobalTheory.AllWt.ptF z ≫ Z.jQ) : z'.x = z.x := by
  have := Z.jQ_open
  rw [← ptF_fst, ← ptF_fst, (cancel_mono _).1 h]

variable (C) in

def rationalEigenFrame : EigFrame Z (algebraMap c.F (Fk C)) (gpt C ≫ C.π ≫ genι Z) := C.f0

theorem tie0 : Comparison₂ (fr0 C) (rationalEigenFrame C) := by
  have hx : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.j = gpt C ≫ C.π ≫ genι Z := by
    rw [Model.j, ← Category.assoc, frame_point_over, Category.assoc]
  exact ⟨rfl, hx, C.flagComponentFramedPoint_frame⟩

variable (C) in

structure Chart (y : C.Y.X) (P : FrPt Xo c (St C y)) (t : Ix Dw → (Fk C)ˣ) : Prop where
  ov : GlobalTheory.AllWt.ptF P ≫ Z.jQ = pt C y ≫ C.π
  bm : BM (toFk C y) t P (fr0 C)

theorem Chart.over_j {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) :
    GlobalTheory.AllWt.ptF P ≫ Z.j = pt C y ≫ C.π ≫ genι Z := by
  rw [Model.j, ← Category.assoc, h.ov, Category.assoc]

theorem Chart.move {y y' : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) (hy : y' ⤳ y) :
    ∃ (sp : St C y →ₐ[c.F] St C y') (P' : FrPt Xo c (St C y')), FrMap sp P P' ∧ Chart C y' P' t ∧
      spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  obtain ⟨sp, h1, h2⟩ := exists_spec hy
  obtain ⟨P', hP⟩ := exists_frMap sp P
  exact ⟨sp, P', hP, ⟨by rw [ptF_map hP.1, Category.assoc, h.ov, ← Category.assoc, h1], BM.cancel hP h.bm h2⟩, h1, h2⟩

end Cpt

section Wit

variable {C : FlagCpt Z e} {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

variable (C) in

structure Wit (p : Sp T ⟶ C.Y.X) (z : FrPt Xo c T) : Type where
  y : C.Y.X
  ψ : St C y →ₐ[c.F] T
  P : FrPt Xo c (St C y)
  t : Ix Dw → (Fk C)ˣ
  t' : Ix Dw → Tˣ
  chart : Chart C y P t
  hp : spMap ψ.toRingHom ≫ pt C y = p
  bm : BM ψ t' P z

variable {p : Sp T ⟶ C.Y.X} {z : FrPt Xo c T}

theorem Wit.ov (w : Wit C p z) : GlobalTheory.AllWt.ptF z ≫ Z.jQ = p ≫ C.π := by
  rw [ptF_map w.bm.x_eq, Category.assoc, w.chart.ov, ← Category.assoc, w.hp]

theorem Wit.transfer [IsLocalRing T] (w : Wit C p z) {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ}
    (h : Chart C y P t) {ψ : St C y →ₐ[c.F] T} (hp : spMap ψ.toRingHom ≫ pt C y = p) :
    ∃ t', BM ψ t' P z ∧ ∀ (ex : Ix Dw → ℤ) a₁ a₂, toFk C w.y a₁ * chi ex w.t = toFk C y a₂ * chi ex t →
      chi ex w.t' * w.ψ a₁ = chi ex t' * ψ a₂ := by
  obtain ⟨y', χ, hχ, hy'⟩ := exists_factor p (by rw [← Category.assoc]; exact str_of_over w.ov)
  obtain ⟨s₁, P₁, a1, a2, a3, a4⟩ := w.chart.move (hy' ▸ specializes_of w.hp (IsLocalRing.closedPoint T) : y' ⤳ w.y)
  obtain ⟨s₂, P₂, b1, b2, b3, b4⟩ := h.move (hy' ▸ specializes_of hp (IsLocalRing.closedPoint T) : y' ⤳ y)
  have e1 : ∀ a, χ (s₁ a) = w.ψ a := fun a => DFunLike.congr_fun
    (hom_eq (ψ := χ.toRingHom.comp s₁.toRingHom) (by rw [← sp_comp, Category.assoc, a3, hχ, w.hp])) a
  have e2 : ∀ a, χ (s₂ a) = ψ a := fun a => DFunLike.congr_fun
    (hom_eq (ψ := χ.toRingHom.comp s₂.toRingHom) (by rw [← sp_comp, Category.assoc, b3, hχ, hp])) a
  obtain ⟨v, hv, ht⟩ := BM.descend (toFk_injective C _) (x_eq_of_over (a2.ov.trans b2.ov.symm)) b2.bm a2.bm
  have k1 : BM χ (w.t' * umap χ v) P₂ z := (BM.of_frBor hv).comp (BM.cancel a1 w.bm e1) fun _ => rfl
  have k2 := (BM.of_frMap b1).comp k1 e2
  have e3 : umap χ (1 : Ix Dw → (St C _)ˣ) = 1 := funext fun i => map_one _
  rw [e3, mul_one] at k2
  refine ⟨_, k2, fun ex a₁ a₂ ha => ?_⟩
  rw [ht, chi_mul, Units.val_mul, chi_umap, ← a4, ← b4] at ha
  have ha' : s₁ a₁ = s₂ a₂ * (chi ex v : (St C _)ˣ) := toFk_injective C _ (by
    rw [map_mul]
    refine (chi ex w.t).isUnit.mul_right_cancel ?_
    rw [ha]; ring)
  rw [chi_mul, Units.val_mul, chi_umap, ← e1, ← e2, ha', map_mul]
  ring

theorem carries_iff {k : Type} [Field k] {p : Sp k ⟶ C.Y.X} {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} :
    C.Carries p g ↔ ∃ (y : C.Y.X) (ψ : St C y →+* k) (φ₁ : c.F →+* St C y)
    (f : EigFrame Z φ₁ (pt C y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fk C)ˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), p = spMap ψ ≫ pt C y ∧
      f.Tri (toFk C y).toRingHom (rationalEigenFrame C) t ∧ f.Tri ψ g t' := Iff.rfl

theorem Wit.carries {k : Type} [Field k] [Algebra c.F k] {p : Sp k ⟶ C.Y.X} {z : FrPt Xo c k} (w : Wit C p z)
    {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} (hg : Comparison₂ z g) : C.Carries p g := by
  obtain ⟨f, hf⟩ := exists_tie_frame w.P w.chart.over_j
  exact carries_iff.2 ⟨w.y, w.ψ.toRingHom, _, f, _, _, w.hp.symm, hf.tri_of_bm tie0 w.chart.bm, hf.tri_of_bm hg w.bm⟩

theorem dual_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

end Wit

section Global

variable {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (ex : Ix Dw → ℤ)
  (s : ∀ k, Fk (Φ.C k)) {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

def Val (z : FrPt Xo c T) (v : T) : Prop :=
  ∃ (i : U.Comp) (p : Sp T ⟶ (Φ.C i).Y.X) (w : Wit (Φ.C i) p z) (a : St (Φ.C i) w.y),
    toFk _ w.y a * chi ex w.t = s i ∧ v = chi ex w.t' * w.ψ a

def Rep (P : FrPt Xo c T) (r : T) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (φ : T →ₐ[c.F] k) (z : FrPt Xo c k), FrMap φ P z →
    Val Φ ex s z (φ r)

variable {Φ ex s}

theorem Val.comp {z : FrPt Xo c T} {v : T} (h : Val Φ ex s z v) {χ : T →ₐ[c.F] T'} {u : Ix Dw → T'ˣ}
    {z' : FrPt Xo c T'} (hz : BM χ u z z') : Val Φ ex s z' (chi ex u * χ v) := by
  obtain ⟨i, p, w, a, h1, rfl⟩ := h
  refine ⟨i, _, ⟨w.y, χ.comp w.ψ, w.P, w.t, _, w.chart, rfl, w.bm.comp hz fun _ => rfl⟩, a, h1, ?_⟩
  show _ = (chi ex (u * umap χ w.t') : T') * χ (w.ψ a)
  rw [chi_mul, Units.val_mul, chi_umap, map_mul, mul_assoc]

theorem Val.map {z : FrPt Xo c T} {v : T} (h : Val Φ ex s z v) {χ : T →ₐ[c.F] T'}
    {z' : FrPt Xo c T'} (hz : FrMap χ z z') : Val Φ ex s z' (χ v) := by
  simpa [chi_one] using h.comp (BM.of_frMap hz)

theorem lift_frame {k : Type} [Field k] [Algebra c.F k] (z : FrPt Xo c k) :
    ∃ g : EigFrame Z (algebraMap c.F k) ((GlobalTheory.AllWt.ptF z ≫ Z.jQ) ≫ genι Z), Comparison₂ z g :=
  exists_tie_frame z (by rw [Model.j, Category.assoc])

theorem Val.unique {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] {z : FrPt Xo c k} {v v' : k}
    (h : Val Φ ex s z v) (h' : Val Φ ex s z v') : v = v' := by
  obtain ⟨i, p, w, a, h1, rfl⟩ := h
  obtain ⟨i', p', w', a', h1', rfl⟩ := h'
  obtain ⟨g, hg⟩ := lift_frame (Z := Z) z
  have e0 : (⟨i, p⟩ : Σ i : U.Comp, (Sp k ⟶ (Φ.C i).Y.X)) = ⟨i', p'⟩ :=
    (Φ.lifts k _ _ (str_of_over rfl) g).unique ⟨w.ov.symm, w.carries hg⟩ ⟨w'.ov.symm, w'.carries hg⟩
  cases e0
  obtain ⟨t', k1, k2⟩ := w.transfer w'.chart w'.hp
  rw [k2 ex a a' (h1.trans h1'.symm), k1.unique w'.bm]

theorem Rep.map {P : FrPt Xo c T} {r : T} (h : Rep Φ ex s P r) {χ : T →ₐ[c.F] T'} {Q : FrPt Xo c T'}
    (hQ : FrMap χ P Q) : Rep Φ ex s Q (χ r) := fun k _ _ _ φ z hz =>
  h k (φ.comp χ) z (frMap_comp hQ hz fun _ => rfl)

theorem Rep.unique [IsReduced T] {P : FrPt Xo c T} {r r' : T} (h : Rep Φ ex s P r) (h' : Rep Φ ex s P r') : r = r' := by
  refine sub_eq_zero.1 (GeometricValues.eq_zero_of_forall_algClosed (K := c.F) _ fun k _ _ _ φ => ?_)
  obtain ⟨z, hz⟩ := exists_frMap φ P
  rw [map_sub, (h k φ z hz).unique (h' k φ z hz), sub_self]

theorem Val.rep {P : FrPt Xo c T} {r : T} (h : Val Φ ex s P r) : Rep Φ ex s P r := fun _ _ _ _ _ _ hz => h.map hz

variable (hex : ex none = 0)
  (hs : ∀ k (y : (Φ.C k).Y.X), (Φ.C k).π y ∉ genBd Z → ((Φ.C k).LEx ex).RegularAt y (s k))

include hex hs

end Global

end Descent

end GlobalTheory.ShFam
