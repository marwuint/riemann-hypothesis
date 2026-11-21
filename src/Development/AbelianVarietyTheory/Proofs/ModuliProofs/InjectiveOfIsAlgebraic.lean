import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TateUniformizationInput
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfPowEqInt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcInputCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Classes

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

def GtMod (_oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F] : Type := GtPtF D F

variable (hB : D.TauBimult) (oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F]

instance : AddCommGroup (GtMod oa F) := gtGroup D F

instance : Module O (GtMod oa F) := gtModule globalFns_holds oa F

def relMap (k : ℕ) : D.X →ₗ[O] D.X × GtMod oa F where
  toFun z := (k • z, iota hB F z)
  map_add' a b := Prod.ext (nsmul_add _ _ _) (map_add (iota hB F) a b)
  map_smul' a z := Prod.ext (smul_comm k a z) (iota_smul globalFns_holds oa hB a z)

variable {F} {k : ℕ}

def cls (p : QkPt D F k) : (D.X × GtMod oa F) ⧸ LinearMap.range (relMap hB oa F k) :=
  Submodule.Quotient.mk (p.y, p.g)

theorem equiv_iff_cls (p q : QkPt D F k) : QkPt.Equiv D F p q ↔ cls hB oa p = cls hB oa q := by
  rw [equiv_iff hB, cls, cls, eq_comm, Submodule.Quotient.eq]
  refine exists_congr fun z => ?_
  rw [eq_sub_iff_add_eq', Prod.ext_iff]
  exact and_congr eq_comm eq_comm

theorem add_iff_cls (p p' q : QkPt D F k) :
    Geo.Tor.QkAdd p p' q ↔ cls hB oa p + cls hB oa p' = cls hB oa q := by
  rw [TorusExt.qkAdd_iff hB, equiv_iff_cls hB oa]; rfl

theorem zero_iff_equiv (p : QkPt D F k) : TateUniformizationInput.QkZero p ↔ QkPt.Equiv D F (qkZero hB F k) p := by
  rw [equiv_iff hB]
  refine exists_congr fun z => and_congr ?_ ?_
  · rw [qkZero, qkMk_y, zero_add]
  · rw [qkZero, qkMk_g, zero_add, isIota_iff_eq hB]

theorem zero_iff_cls (p : QkPt D F k) : TateUniformizationInput.QkZero p ↔ cls hB oa p = 0 := by
  rw [zero_iff_equiv hB, equiv_iff_cls hB oa, eq_comm]; rfl

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem isRatio_ext {p p' : QkPt D F k} {z : F} (h : QkPairing.IsRatio p p' z) :
    QkPairing.IsRatio (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  intro T σ y J hJ
  have e := h T (σ ≫ extMap f hf) y J hJ
  have v : ∀ (g : GtPtF D F) χ, val ((gtExt D f hf g).s χ) σ.left y J = val (g.s χ) (σ ≫ extMap f hf).left y J :=
    fun g χ => (val_corr hJ (((eq_gtExt_iff f hf g _).1 rfl).2 χ) _).trans (val_pull hJ _ _ _)
  have w : gs σ.left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (f z)) =
      gs (σ ≫ extMap f hf).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
    refine Eq.trans (congrArg (gs σ.left y ⊤) ?_) (gs_pull σ.left (spMap f) y ⊤ trivial _)
    exact congrArg (fun g => g.hom z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [qkExt, qkMk_y, qkMk_g]
  rw [v, v, w, gtExt_b, gtExt_b, ← Category.assoc, ← Category.assoc]
  exact e

theorem weil_ext (k : ℕ) (hk : 1 ≤ k) (p p' : QkPt D F k) (z : F) (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  obtain ⟨u, hu⟩ := QkPairing.exists_ratio p p'
  obtain rfl := QkPairing.weil_unique globalFns_holds abelianSchemeLaws_all.2.secTwist hB hk p p' h
    (QkPairing.weil_of_ratio globalFns_holds p p' hu)
  exact QkPairing.weil_of_ratio globalFns_holds _ _ (ζ := Units.map f.toMonoidHom u) (isRatio_ext hB f hf hu)

end Classes

theorem injective_of_isAlgebraic {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [CharZero B]
    (h : ∀ x : A, IsAlgebraic ℤ x) (f : A →+* B) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun x hx => by_contra fun h0 => ?_
  refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker f) h0 hx (h x) (eq_bot_iff.2 fun n hn => ?_)
  have : f (n : A) = 0 := hn
  rw [map_intCast] at this
  exact Int.cast_eq_zero.1 this

theorem finrank_torusLieEigen {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] (k : Type) [Field k] [CharZero k] [Module.Finite ℤ X] (τ : 𝓞 E →+* k) :
    Module.finrank k (TateUniformizationInput.torusLieEigen H X k τ) = Module.finrank (𝓞 E) X := by
  let σ : 𝓞 E →+* k := τ.comp (H.bar : 𝓞 E →+* 𝓞 E)
  let _ := σ.toAlgebra
  have hσ : Function.Injective σ := injective_of_isAlgebraic (fun x => Algebra.IsAlgebraic.isAlgebraic x) σ
  have : FaithfulSMul (𝓞 E) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hσ
  have : Module.Finite (𝓞 E) X := .of_restrictScalars_finite ℤ _ _
  let e : TateUniformizationInput.torusLieEigen H X k τ ≃ₗ[k] (X →ₗ[𝓞 E] k) :=
    { toFun := fun v => ⟨⟨v.1, map_add v.1⟩, fun a x => by
        have := v.2 (H.bar a) x
        rw [TorusGraphMaps.bar_bar] at this
        exact this⟩
      invFun := fun v => ⟨v.toAddMonoidHom, fun a x => by
        refine (v.map_smul _ _).trans ?_
        show τ (H.bar (H.bar a)) * _ = _
        rw [TorusGraphMaps.bar_bar]; rfl⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, (LinearMap.liftBaseChangeEquiv k).finrank_eq]
  refine Subspace.dual_finrank_eq.trans ?_
  exact (TensorProduct.isBaseChange (𝓞 E) X k).finrank_eq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Data

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]

open Classical in

theorem det_iff [CharZero F] (ρ : F) :
    (letI := H.starRing
      ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oa.onB.toRingAct)
        (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧
        n + Module.finrank (𝓞 E) P.X = if τ H.rt = ρ then D.p else D.q) ↔ TateUniformizationInput.GtDetCond D oa F ρ := by
  have e : spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) = DegPre.jFR (R := R) F := by
    rw [DegPre.jFR, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine forall_congr' fun τ => ?_
  simp only [TateUniformizationInput.GtLieMult, finrank_torusLieEigen]
  rw [e]
  by_cases h : τ H.rt = ρ
  · rw [if_pos h]; exact ⟨fun k => ⟨fun _ => k, fun k' => absurd h k'⟩, fun k => k.1 h⟩
  · rw [if_neg h]; exact ⟨fun k => ⟨fun k' => absurd k' h, fun _ => k⟩, fun k => k.2 h⟩

variable (hB : P.TauBimult)

def toQTateIso (I : TateIsoQ D P oa F) : TateUniformizationInput.QTateIso D oa F where
  ζ n := I.ζ n
  ζ_prim n := I.ζ_prim n n.pos
  ζ_pow n m := I.ζ_pow n m n.pos m.pos
  ev n := I.ev n
  add n := I.add n n.pos
  lin n x a := letI := H.starRing; (DegActCompare.qkAct_iff oa x _ _).1 (I.lin n n.pos x a)
  ker n a := by
    letI := H.starRing
    have h := (add_iff_cls hB oa _ _ _).1 (I.add n n.pos 0 0)
    rw [add_zero, add_eq_left] at h
    rw [zero_iff_cls hB oa, ← h, ← equiv_iff_cls, I.ker n n.pos]
    simp only [zero_add]
  onto n := I.onto n n.pos
  tower n m a := ⟨rfl, I.tower n m n.pos m.pos a⟩
  isom n := I.isom n n.pos

def evNat (J : TateUniformizationInput.QTateIso D oa F) (n : ℕ) (a : D.La) : QkPt P F n :=
  if h : 0 < n then J.ev ⟨n, h⟩ a else qkZero hB F n

theorem evNat_pos (J : TateUniformizationInput.QTateIso D oa F) {n : ℕ} (h : 0 < n) : evNat hB J n = J.ev ⟨n, h⟩ :=
  funext fun _ => dif_pos h

include hB in
theorem equiv_ev_iff (J : TateUniformizationInput.QTateIso D oa F) (n : ℕ+) (a b : D.La) :
    QkPt.Equiv P F (J.ev n a) (J.ev n b) ↔ ∃ e, a = b + (n : ℕ) • e := by
  letI := H.starRing
  have k := (add_iff_cls hB oa _ _ _).1 (J.add n (a - b) b)
  rw [sub_add_cancel] at k
  rw [equiv_iff_cls hB oa, ← k, add_eq_right, ← zero_iff_cls, J.ker]
  exact exists_congr fun e => sub_eq_iff_eq_add'

def ofQTateIso (J : TateUniformizationInput.QTateIso D oa F) : TateIsoQ D P oa F where
  ζ n := if h : 0 < n then J.ζ ⟨n, h⟩ else 1
  ζ_prim n h := by rw [dif_pos h]; exact J.ζ_prim ⟨n, h⟩
  ζ_pow n m h h' := by rw [dif_pos h, dif_pos (Nat.mul_pos h h')]; exact J.ζ_pow ⟨n, h⟩ ⟨m, h'⟩
  ev := evNat hB J
  add n h := by rw [evNat_pos hB J h]; exact J.add ⟨n, h⟩
  lin n h x a := by
    letI := H.starRing
    rw [evNat_pos hB J h]; exact (DegActCompare.qkAct_iff oa x _ _).2 (J.lin ⟨n, h⟩ x a)
  ker n h a b := by rw [evNat_pos hB J h]; exact equiv_ev_iff hB J ⟨n, h⟩ a b
  onto n h := by rw [evNat_pos hB J h]; exact J.onto ⟨n, h⟩
  tower n m h h' a := by
    rw [evNat_pos hB J h, evNat_pos hB J (Nat.mul_pos h h')]; exact (J.tower ⟨n, h⟩ ⟨m, h'⟩ a).2
  isom n h := by rw [evNat_pos hB J h, dif_pos h]; exact J.isom ⟨n, h⟩

def SameIso (I : TateIsoQ D P oa F) (J : TateUniformizationInput.QTateIso D oa F) : Prop :=
  ∀ n : ℕ+, I.ζ n = J.ζ n ∧ I.ev n = J.ev n

theorem sameIso_of (J : TateUniformizationInput.QTateIso D oa F) : SameIso (ofQTateIso hB J) J := fun n =>
  ⟨dif_pos n.pos, evNat_pos hB J n.pos⟩

end Data

section Lev

variable (D : Datum H) (l : Level H)

abbrev halfLat : Submodule (𝓞 E) D.La := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)

end Lev

section Level

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {l : Level H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (hB : P.TauBimult)

variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

omit [Module (𝓞 E) P.X] in

theorem qkExt_qkExt {F'' : Type} [Field F''] [Algebra (FractionRing R) F''] (g : F' →+* F'')
    (hg : g.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F'') {k : ℕ} {p : QkPt P F k}
    {q : QkPt P F'' k} (h : QkExt (g.comp f) p q) : q = qkExt hB g hg (qkExt hB f hf p) := by
  refine DegActCompare.qkExt_unique h ?_
  have h₁ := (TorusExt.qkExt_iff hB f hf p _).2 rfl
  have h₂ := (TorusExt.qkExt_iff hB g hg (qkExt hB f hf p) _).2 rfl
  have e : spMap (g.comp f) = spMap g ≫ spMap f := by rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
  refine ⟨rfl, by rw [h₂.2.1, h₁.2.1, e, Category.assoc], fun χ => corr_of_val P.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h₂.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h₁.2.2 χ) _).trans
    ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
  rw [e, Category.assoc]

end Level

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

open Classical in

theorem geom_of_input (x : TateUniformizationInput.ArcInput D c β O' b) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing O') F] (r z : O) (hr : ((β r : c.F) : ℂ) = H.rt0) (hz : ((β z : c.F) : ℂ) = zeta l.A)
    (f : O' →+* F) (hf : f = (algebraMap (FractionRing O') F).comp (algebraMap O' _)) : letI := H.starRing
    (∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct x.ac.onB.toRingAct) (spMap f) τ n ∧
      n + Module.finrank (𝓞 E) x.P.X = if τ H.rt = f (b r) then D.p else D.q) ∧
    ∃ I : TateIsoQ D x.P x.ac F, (I.ζ l.A : F) = f (b z) ∧
      (∀ a q, QkExt (algebraMap _ F) (x.lev.etaA a) q → QkPt.Equiv x.P F q (I.ev l.A a)) ∧
      ∀ a ∈ halfLat D l, ∀ q, QkExt (algebraMap _ F) (x.lev.eta a) q → QkPt.Equiv x.P F q (I.ev l.M a) := by
  letI := H.starRing
  subst hf
  have hB := x.tau_bimult
  have := x.charZero
  let i : AlgebraicClosure (FractionRing O') →+* F :=
    (IsAlgClosed.lift : AlgebraicClosure (FractionRing O') →ₐ[FractionRing O'] F)
  have hi₀ : ∀ y, i (algebraMap (FractionRing O') _ y) = algebraMap (FractionRing O') F y := fun y =>
    (IsAlgClosed.lift : AlgebraicClosure (FractionRing O') →ₐ[FractionRing O'] F).commutes y
  have hi : i.comp (algebraMap (FractionRing O') _) = algebraMap (FractionRing O') F := RingHom.ext hi₀
  constructor
  · intro σ
    obtain ⟨τ, rfl⟩ := DetExtend.exists_factor i σ
    obtain ⟨n, h₁, h₂⟩ := (det_iff _).2 x.det τ
    have := x.P.P.isAb.smooth
    rw [x.gam_rt r hr] at h₂
    refine ⟨n, ?_, h₂.trans (if_congr ?_ rfl rfl)⟩
    · have e : spMap ((algebraMap (FractionRing O') F).comp (algebraMap O' _)) = spMap i ≫
          spMap ((algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))).comp (algebraMap O' _)) := by
        rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hi]
      rw [e]
      exact (DetExtend.lieMult_extend i _ _ τ n).2 h₁
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← hi₀, i.injective.eq_iff]
  · obtain ⟨J, hζ, hA, hM⟩ := x.induced
    have key : ∀ (n : ℕ+) (p : QkPt x.P (FractionRing O') n) (a : D.La),
        TorusGraphMaps.QkMap (Algebra.ofId (FractionRing O') _) p (J.ev n a) → ∀ q, QkExt (algebraMap _ F) p q →
        QkPt.Equiv x.P F q (qkExt hB i hi ((ofQTateIso hB J).ev n a)) := fun n p a h q hq => by
      have h₀ : (algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))).comp
        (algebraMap (FractionRing O') (FractionRing O')) = algebraMap _ _ := RingHom.ext fun _ => rfl
      rw [← hi] at hq
      rw [qkExt_qkExt hB _ h₀ i hi hq, (sameIso_of hB J n).2]
      exact qkExt_congr hB i hi ((DegActCompare.forall_qkExt_iff hB _ _ _).2 h _
        ((TorusExt.qkExt_iff hB _ h₀ _ _).2 rfl))
    refine ⟨ArcExt.tateExt i hi hB abelianSchemeLaws_all.1 (ofQTateIso hB J) (weil_ext hB i hi), ?_,
      fun a => key (TateUniformizationInput.levelA l) _ a (hA a), fun a ha => key (TateUniformizationInput.levelM l) _ a (hM a ha)⟩
    show i ((ofQTateIso hB J).ζ (TateUniformizationInput.levelA l)) = _
    rw [(sameIso_of hB J _).1, hζ, x.gam_zeta z hz, hi₀, RingHom.comp_apply]

def toArcIn (x : TateUniformizationInput.ArcInput D c β O' b) : ArcIn D l β O' b where
  D₀ := x.P
  oa := x.ac
  nontriv := x.nontriv
  even := x.psi_even
  bimult := x.tau_bimult
  gen y := (DegActCompare.psiUnitOn_iff _ y isOpen_univ).2 (x.psi_gen y)
  w0 := (DegActCompare.psiW0_host_iff H x.ac).2 x.through
  be := x.be
  be_symm := x.be_symm
  be_pos := x.be_pos
  be_adj := x.be_adj
  be_dvd := x.be_dvd
  eta := x.lev.eta
  etaA := x.lev.etaA
  geom F _ _ _ r z hr hz f hf := geom_of_input x F r z hr hz f hf

end ThetaShiftProofs

section Main

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

structure Core (D : Datum H) (l : Level H) (O' : Type) [CommRing O'] [IsDomain O'] where
  P : DegPre O'
  [mod : Module (𝓞 E) P.X]
  ac : letI := H.starRing; P.OAct (𝓞 E)
  be : LinearMap.BilinForm ℤ P.X
  eta : halfLat D l → QkPt P (FractionRing O') l.M
  etaA : D.La → QkPt P (FractionRing O') l.A

def coreOfArcIn (a : ArcIn D l β O' b) : Core D l O' :=
  { P := a.D₀, ac := a.oa, be := a.be, eta := fun v => a.eta v, etaA := a.etaA }

def coreOfInput (x : TateUniformizationInput.ArcInput D c β O' b) : Core D l O' :=
  { P := x.P, ac := x.ac, be := x.be, eta := fun v => x.lev.eta v, etaA := x.lev.etaA }

theorem core_toArcIn (x : TateUniformizationInput.ArcInput D c β O' b) : coreOfArcIn (toArcIn x) = coreOfInput x := rfl

end Main

end GlobalTheory.ArcInputCompare
