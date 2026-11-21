import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransitionUniqueAndPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValues
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTangentOfUniqueIntegralLiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentFamilyOfUniqueLiftPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Val

variable {F : Type} [Field F] {X Y : Scheme.{0}}

theorem valF_appLE {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_mul {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a * b) = valF x U a * valF x U b := by
  simp only [valF, dif_pos h, map_mul]

theorem valF_mul_inv {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valF x U a.val * valF x U (a⁻¹).val = 1 := by
  rw [← valF_mul h, a.mul_inv]
  simp only [valF, dif_pos h, map_one]

theorem valF_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* F) (s : Γ(X, V)) :
    valF (spMap χ ≫ hV.fromSpec) V s = χ s := by
  have h0 : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V := fun q _ => h0 (Set.mem_univ (spMap χ q))
  rw [valF, dif_pos h]
  have e : (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom = CommRingCat.ofHom χ := by
    have e1 : hV.fromSpec.appLE V ⊤ h0 = (Scheme.ΓSpecIso Γ(X, V)).inv := by
      rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg _ ((Spec Γ(X, V)).presheaf.map_id _)).trans (Category.comp_id _)
    rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h0 le_rfl, e1, Category.assoc, Iso.inv_comp_eq]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  exact congrArg (fun g => g.hom s) e

theorem exists_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] (w : Sp R ⟶ X)
    (h : ⊤ ≤ w ⁻¹ᵁ V) : ∃ χ : Γ(X, V) →+* R, spMap χ ≫ hV.fromSpec = w := by
  have h' : Set.range w ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hV.range_fromSpec]
    exact h (Set.mem_univ q)
  exact ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec w h')).hom,
    (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩

theorem le_of_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] {w : Sp R ⟶ X}
    {χ : Γ(X, V) →+* R} (h : spMap χ ≫ hV.fromSpec = w) : ⊤ ≤ w ⁻¹ᵁ V := fun q _ =>
  h ▸ hV.fromSpec_preimage_self.ge (Set.mem_univ (spMap χ q))

theorem mono_fromSpec {V : X.Opens} (hV : IsAffineOpen V) : Mono hV.fromSpec := inferInstance

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Frames

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}

theorem eig_iff {R : Type} [CommRing R] {x : Sp R ⟶ X} (v : TanM x t.G) (a : 𝓞 E) (s : R) :
    (tv v).left ≫ (t.act.act a).left = spMap (epsMul s) ≫ (tv v).left ↔ actR t.act a v = s • v :=
  ⟨fun h => tan_ext h, fun h => congrArg (fun z => (tv z).left) h⟩

theorem frame_ind {k : Type} [Field k] {f : c.F →+* k} {x : Sp k ⟶ X} {u : Vecs Dw t k}
    (h : GlobalTheory.LocM.IsFrame t f x u) (τ : E →+* ℂ) : Ind t x (u τ) := by
  refine ⟨fun i => (h.1 τ i).1, fun cf cf' w h1 h2 => ?_⟩
  obtain ⟨U, hU⟩ := exists_tan fun i => (h.1 τ i).1
  have e := (comb_iff U cf w).1 (hU ▸ h1)
  refine (h.2 τ w (e ▸ isTan_tv _) fun a => ?_).unique h1 h2
  rw [e, eig_iff, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, (eig_iff (U i) a _).1 (congrFun hU i ▸ (h.1 τ i).2 a)]

variable {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)

include hx

theorem comb_push {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t'.G.left)} (hu : ∀ i, IsTanAtG t' x' (u i))
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : IsTanAtG t' x' w) (cf : Fin m → R) :
    IsCombAtG t x (fun i => u i ≫ mu.φ) cf (w ≫ mu.φ) ↔ IsCombAtG t' x' u cf w := by
  refine (GlobalTheory.LieMet.isComb_iff (fun i => pushE mu x' hx (tanOf (hu i))) cf (pushE mu x' hx (tanOf hw))).trans
    (Iff.trans ?_ (GlobalTheory.LieMet.isComb_iff (fun i => tanOf (hu i)) cf (tanOf hw)).symm)
  simp only [← map_smul, ← map_sum, EmbeddingLike.apply_eq_iff_eq]

theorem frame_push {f' : c'.F →+* R} {f : c.F →+* R} (hf : ∀ τ a, f (embK c τ a) = f' (embK c' τ a))
    {u : Vecs Dw t' R} (h : GlobalTheory.LocM.IsFrame t' f' x' u) : GlobalTheory.LocM.IsFrame (Dw := Dw) t f x fun τ i => u τ i ≫ mu.φ := by
  refine ⟨fun τ i => ⟨isTan_push mu x' hx (h.1 τ i).1, fun a => ?_⟩, fun τ w hw he => ?_⟩
  · rw [Category.assoc, ← mu.act, ← Category.assoc, (h.1 τ i).2, hf, Category.assoc]
  · obtain ⟨v, hv⟩ := (pushE mu x' hx).surjective (tanOf hw)
    obtain rfl : (tv v).left ≫ mu.φ = w := congrArg (fun z => (tv z).left) hv
    refine (existsUnique_congr fun cf => comb_push mu hx (fun i => (h.1 τ i).1) (isTan_tv v) cf).2
      (h.2 τ _ (isTan_tv v) fun a => (eig_iff v a _).2 ((pushE mu x' hx).injective ?_))
    rw [pushE_act, map_smul, ← hf]
    exact (eig_iff _ a _).1 (he a)

end Frames

section Steps

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l} {p : ℕ}

theorem lnStep_push {g : X' ⟶ X} (mu : SABMap t' t g) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (b : Bool) (xO : Sp ↥(intO C) ⟶ X')
    (hO : ∀ y : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ xO ≫ g → y = xO ≫ g)
    {u : Vecs Dw t' C} (hu : ∀ τ i, IsTanAtG t' (spMap (intO C).subtype ≫ xO) (u τ i)) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    lnStep t' (spMap (intO C).subtype ≫ xO) u p b st =
      lnStep (Dw := Dw) t (spMap (intO C).subtype ≫ xO ≫ g) (fun τ i => u τ i ≫ mu.φ) p b st := by
  have key := fun {m : ℕ} {v : Fin m → (Sp (DualNumber C) ⟶ t'.G.left)} =>
    grNorm_push (v := v) mu (Category.assoc _ _ _) (GlobalTheory.T.isTangent_of_unique_integral_lift E H X X' t t' g mu C p b xO hO)
  rcases st with ⟨τ, k⟩ | k
  · simp only [lnStep, key (hu τ)]
  · simp only [lnStep, key (v := fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) fun i => hu _ _]

theorem lnStep_tri (hB : HTBoundSt) (hp : p.Prime) (C : Formalism.MainNotions.DIV.Cons.SCF p) (b : Bool) (xO : Sp ↥(intO ↥C.S) ⟶ X)
    (hO : ∀ y : Sp ↥(intO ↥C.S) ⟶ X, spMap (intO ↥C.S).subtype ≫ y = spMap (intO ↥C.S).subtype ≫ xO → y = xO)
    {f : c.F →+* ↥C.S} {u u' : Vecs Dw t ↥C.S} (hu : GlobalTheory.LocM.IsFrame t f (spMap (intO ↥C.S).subtype ≫ xO) u)
    (hu' : GlobalTheory.LocM.IsFrame t f (spMap (intO ↥C.S).subtype ≫ xO) u')
    (h : ∀ τ, Tri t (spMap (intO ↥C.S).subtype ≫ xO) (u τ) (u' τ)) {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}
    (hx : letterOf Dw st = some x) {cf : Fin (Dw.mult x.1) → ↥C.S}
    (hc : IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) (u x.1) cf (u' x.1 x.2)) :
    lnStep t (spMap (intO ↥C.S).subtype ≫ xO) u' p b st =
      Real.log ‖cf x.2‖ + lnStep t (spMap (intO ↥C.S).subtype ≫ xO) u p b st := by
  obtain ⟨h0, h1⟩ := (h x.1).diag (frame_ind hu _) (frame_ind hu' _) hc
  have pos := _root_.GlobalTheory.GrNormPos.grNorm_pos hB E H X t p C b xO hp hO
  rcases st with ⟨τ, k⟩ | k
  · by_cases hk : k < Dw.mult τ
    · simp only [letterOf, dif_pos hk, Option.some.injEq] at hx
      subst hx
      simp only [lnStep, dif_pos hk]
      rw [(h τ).grNorm_eq (frame_ind hu _) (frame_ind hu' _) _ hc, Real.log_mul (norm_ne_zero_iff.2 h0)
        (pos _ _ (frame_ind hu τ).1 (frame_ind hu τ).2 _).ne', add_sub_assoc]
    · simp [letterOf, hk] at hx
  · obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨i1, c1⟩ := _root_.GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c X t _ f _ u hu
    have I1 : Ind t _ _ := ⟨fun i => (hu.1 _ _).1, i1⟩
    have I2 : Ind t _ _ := ⟨fun i => (hu'.1 _ _).1, (_root_.GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c X t _ f _ u' hu').1⟩
    have T : Tri t _ (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
        (fun i => u' ((letters Dw).get i).1 ((letters Dw).get i).2) := fun j => by
      obtain ⟨d, d1, d2⟩ := h ((letters Dw).get j).1 ((letters Dw).get j).2
      obtain ⟨e, e1, -, e2⟩ := c1 j d _ d1 d2
      exact ⟨e, e1, e2⟩
    obtain ⟨e, -, e1, e2⟩ := c1 ⟨k, hk⟩ cf _ h1 hc
    simp only [lnStep, dif_pos hk]
    rw [T.grNorm_eq I1 I2 _ e2, e1]
    exact Real.log_mul (norm_ne_zero_iff.2 h0) (pos _ _ I1.1 I1.2 _).ne'

end Steps

section Models

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem chart_frame (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    GlobalTheory.LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (w ≫ Z.π) ((Z.fr a).bc φ) := by
  rw [← h, Category.assoc]
  exact _root_.GlobalTheory.ShFam.Pad.isFrame_baseChange E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)

theorem affineOpenChart_comp_structure_eq_spMap (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    w ≫ Z.π ≫ (Y Z.i).s = spMap (φ.comp (Z.alg a)) ≫ spMap (Z.i.c.V W).subtype := by
  rw [Z.π_s, ← h, Category.assoc, Z.alg_s, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, RingHom.comp_assoc]

theorem range_opn (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) : Set.range w ⊆ Z.opn := by
  rintro _ ⟨q, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, le_of_fromSpec (Z.U a).2 h (Set.mem_univ q)⟩

theorem exists_open_lift (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    ∃ y : Sp R ⟶ (Xo Z.i.l).XF Z.i.c, y ≫ (Y Z.i).j = w ≫ Z.π := by
  have := (Y Z.i).jQ_open
  let q : Sp R ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) _ ((Category.assoc _ _ _).trans (affineOpenChart_comp_structure_eq_spMap Z h))
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z h ⟨z, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  exact ⟨IsOpenImmersion.lift _ q hr, by rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, IsOpenImmersion.lift_fac_assoc, hq]⟩

theorem tri_of_sameFlag {X : Scheme.{0}} {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {u u' : Vecs Dw t k}
    {ty : (E →+* ℂ) → Finset ℕ} (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ ty τ) (h : SameFlag ty t x u u') (τ : E →+* ℂ) :
    Tri t x (u τ) (u' τ) := fun j => h τ (j + 1) (hty τ _ j.2) j (Nat.lt_succ_self _)

theorem chart_tri (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) {k : Type} [Field k] {a a' : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} {φ' : Γ(Z.X, (Z.U a').1) →+* k} {w : Sp k ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w)
    (h' : spMap φ' ≫ Z.chart a' = w) (τ : E →+* ℂ) :
    Tri (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ τ) ((Z.fr a').bc φ' τ) := by
  have := tri_of_sameFlag hty (Z.glue k a a' φ φ' (h.trans h'.symm)) τ
  rwa [← Category.assoc, h] at this

theorem isReduced_model (Z : Mdl Y i₀) : IsReduced Z.X :=
  have := Z.normal
  inferInstance

theorem isSeparated_base (i : Idx H p) : (Y i).X.IsSeparated := by
  have := projProper _ _ _ (Y i).proj
  exact ⟨by rw [← terminal.comp_from (Y i).s]; infer_instance⟩

theorem ext_unique (i : Idx H p) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ (Y i).X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have := isSeparated_base (Y := Y) i
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem exists_trans (h : N2 Y) {i i₂ : Idx H p} (hl : i.l.Dvd i₂.l) (hc : i.c.F ≤ i₂.c.F) :
    ∃ τ mu, IsTrans (Y := Y) i i₂ τ mu := by
  obtain ⟨-, π, hπ, -⟩ := h
  let b : i.c.V W →+* i₂.c.V W :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i₂.c.V W) fun x => x.2
  obtain ⟨π', mu, r, h⟩ := hπ i i₂ hl hc b fun _ => rfl
  exact ⟨_, mu, b, π', r, fun _ => rfl, h⟩

variable {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)

include hf hT

end Models

end GlobalTheory.ShFam.Pad.Pull
