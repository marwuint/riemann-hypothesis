import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal.Cmp

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C) :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (x : Sp B ⟶ Sp A) : ∃ β : A →+* B, x = spMap β := by
  exact ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem rho_eq_of_ne (hpq : Dw.p ≠ Dw.q) {l₂ : Geo.Tor.Level H} {Xo₂ : Moduli Dw l₂} {π : Xo₂.X ⟶ Xo.X}
    (m : SABMap Xo₂.univ.t Xo.univ.t π) {k : Type} [Field k] [IsAlgClosed k] {x : Sp k ⟶ Xo₂.X}
    {β : KA l →+* k} {β₂ : KA l₂ →+* k} (h : (x ≫ π) ≫ Xo.s = spMap β) (h₂ : x ≫ Xo₂.s = spMap β₂) :
    β (baseKA l).ρ = β₂ (baseKA l₂).ρ := by
  have : CharZero k := (RingHom.charZero_iff β.injective).mp inferInstance
  have hsq1 : (β (baseKA l).ρ) ^ 2 = -(H.d : k) := by
    have e := congrArg β (baseKA l).ρ_sq
    simpa using e
  have hsq2 : (β₂ (baseKA l₂).ρ) ^ 2 = -(H.d : k) := by
    have e := congrArg β₂ (baseKA l₂).ρ_sq
    simpa using e
  let τE : E →ₐ[ℚ] k := IsAlgClosed.lift
  let τ : 𝓞 E →+* k := (τE : E →+* k).comp (algebraMap (𝓞 E) E)
  have ht : (τ H.rt) ^ 2 = -(H.d : k) := by
    have e := congrArg τ H.rt_sq
    simpa using e
  have D1 := (Xo.univ.geom k (x ≫ π) β h).1
  have D2 := (Xo₂.univ.geom k x β₂ h₂).1
  have P : ∀ n, LieMult Xo₂.univ.t.act x τ n ↔ LieMult Xo.univ.t.act (x ≫ π) τ n := fun n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) Xo.X Xo₂.X Xo.univ.t.G Xo₂.univ.t.G π m.cm.F Xo.univ.t.act Xo₂.univ.t.act
      m.cart m.act k x τ n
  let b' : Base l₂ k :=
    { unit := fun n hn => (Nat.cast_ne_zero.mpr hn.ne').isUnit
      ρ := β₂ (baseKA l₂).ρ
      ρ_sq := hsq2
      ζ := β₂ (baseKA l₂).ζ
      ζ_prim := (baseKA l₂).ζ_prim.map_of_injective β₂.injective }
  obtain ⟨o', ⟨om⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) k (baseKA l₂) b' β₂ Xo₂.X (Sp k) Xo₂.s (𝟙 (Sp k)) x rfl rfl
    (by rw [Category.id_comp]; exact h₂) Xo₂.univ
  have P' : ∀ n, LieMult o'.t.act (𝟙 (Sp k)) τ n ↔ LieMult Xo₂.univ.t.act (𝟙 (Sp k) ≫ x) τ n := fun n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) Xo₂.X (Sp k) Xo₂.univ.t.G o'.t.G x om.cm.F Xo₂.univ.t.act o'.t.act
      om.cart om.act k (𝟙 _) τ n
  have U : ∀ n n', LieMult Xo₂.univ.t.act x τ n → LieMult Xo₂.univ.t.act x τ n' → n = n' := by
    intro n n' hn hn'
    have hn2 := (P' n).mpr (by rw [Category.id_comp]; exact hn)
    have hn2' := (P' n').mpr (by rw [Category.id_comp]; exact hn')
    obtain ⟨bn⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o'.t.act τ n).mp hn2
    obtain ⟨bn'⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o'.t.act τ n').mp hn2'
    have e := (Module.finrank_eq_card_basis bn).symm.trans (Module.finrank_eq_card_basis bn')
    simpa using e
  by_contra hne
  have h21 : β₂ (baseKA l₂).ρ = -(β (baseKA l).ρ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq2.trans hsq1.symm) with e | e
    · exact absurd e.symm hne
    · exact e
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (ht.trans hsq1.symm) with e | e
  · have hp : LieMult Xo₂.univ.t.act x τ Dw.p := (P _).mpr ((D1 τ).1 e)
    have hq : LieMult Xo₂.univ.t.act x τ Dw.q := (D2 τ).2 (by rw [e]; exact hne)
    exact hpq (U _ _ hp hq)
  · have e' : τ H.rt = β₂ (baseKA l₂).ρ := e.trans h21.symm
    have hp : LieMult Xo₂.univ.t.act x τ Dw.p := (D2 τ).1 e'
    have hq : LieMult Xo₂.univ.t.act x τ Dw.q := (P _).mpr ((D1 τ).2 (by rw [e']; exact fun h' => hne h'.symm))
    exact hpq (U _ _ hp hq)

private theorem ringHom_KA_ext_of_A_eq_one (hA : l.A = 1) {R : Type} [CommRing R] {β β' : KA l →+* R}
    (h : β (baseKA l).ρ = β' (baseKA l).ρ) : β = β' := by
  have hz : zeta l.A = 1 := by
    rw [hA]
    simp [zeta, Complex.exp_two_pi_mul_I]
  ext ⟨z, hz'⟩
  change z ∈ IntermediateField.adjoin ℚ {H.rt0, zeta l.A} at hz'
  induction hz' using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · have e : (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1 := Subtype.ext hz
      rw [e, map_one, map_one]
  | algebraMap q =>
    show β (algebraMap ℚ (KA l) q) = β' (algebraMap ℚ (KA l) q)
    exact DFunLike.congr_fun (RingHom.ext_rat (β.comp (algebraMap ℚ (KA l))) (β'.comp (algebraMap ℚ (KA l)))) q
  | add x y hx hy ihx ihy =>
    show β (⟨x, hx⟩ + ⟨y, hy⟩) = β' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
    show β (⟨x, hx⟩ * ⟨y, hy⟩) = β' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]
  | inv x hx ih =>
    show β (⟨x, hx⟩⁻¹) = β' (⟨x, hx⟩⁻¹)
    by_cases h0 : (⟨x, hx⟩ : KA l) = 0
    · rw [h0, _root_.inv_zero, map_zero, map_zero]
    · have e1 : β ⟨x, hx⟩ * β (⟨x, hx⟩⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      have e2 : β' ⟨x, hx⟩ * β' (⟨x, hx⟩⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      calc β (⟨x, hx⟩⁻¹) = β (⟨x, hx⟩⁻¹) * (β' ⟨x, hx⟩ * β' (⟨x, hx⟩⁻¹)) := by rw [e2, mul_one]
        _ = (β ⟨x, hx⟩ * β (⟨x, hx⟩⁻¹)) * β' (⟨x, hx⟩⁻¹) := by rw [← ih]; ring
        _ = β' (⟨x, hx⟩⁻¹) := by rw [e1, one_mul]

theorem emb_ext_of_one (hA : l.A = 1) {k : Type} [Field k] {β β' : KA l →+* k}
    (h : β (baseKA l).ρ = β' (baseKA l).ρ) : β = β' := by
  exact ringHom_KA_ext_of_A_eq_one hA h

def OverBase (d : DeltaDat Xo c n) : Prop :=
  ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom

theorem point_over_of_ne (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (d : DeltaDat Xo c n) (h : KA l ≤ KA d.l₂)
    {K : Type} [Field K] (t : Sp K ⟶ d.Xo₂.X) :
    t ≫ d.r ≫ Xo.s = t ≫ d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom := by
  obtain ⟨γ1, e1⟩ := exists_spMap' (t ≫ d.r ≫ Xo.s)
  obtain ⟨γ2, e2⟩ := exists_spMap' (t ≫ d.Xo₂.s)
  have key : γ1 = γ2.comp (IntermediateField.inclusion h).toRingHom := by
    apply emb_ext_of_one hA
    let ι := algebraMap K (AlgebraicClosure K)
    apply ι.injective
    have e := rho_eq_of_ne hpq d.m (x := spMap ι ≫ t) (β := ι.comp γ1) (β₂ := ι.comp γ2)
      (by simp only [Category.assoc]; rw [e1, spMap_comp']) (by rw [Category.assoc, e2, spMap_comp'])
    exact e
  rw [e1, ← Category.assoc, e2, spMap_comp', key]

theorem overBase_of_ne (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (d : DeltaDat Xo c n) : OverBase d := by
  intro h
  have : IsReduced d.Xo₂.X := GlobalTheory.UnivPol.isReduced d.Xo₂
  set f := d.r ≫ Xo.s with hf
  set g := d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom with hg
  have hpt : ∀ p : d.Xo₂.X, d.Xo₂.X.fromSpecResidueField p ≫ f = d.Xo₂.X.fromSpecResidueField p ≫ g :=
    fun p => point_over_of_ne hpq hA d h (K := d.Xo₂.X.residueField p) (d.Xo₂.X.fromSpecResidueField p)
  let φf := ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ f.appTop).hom
  let φg := ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ g.appTop).hom
  have key : ∀ p : d.Xo₂.X, p ∉ d.Xo₂.X.basicOpen (φf (baseKA l).ρ - φg (baseKA l).ρ) := by
    intro p hp
    let t := d.Xo₂.X.fromSpecResidueField p
    have e1 : f.appTop ≫ t.appTop = g.appTop ≫ t.appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hpt p]
    have e2 : t.appTop (φf (baseKA l).ρ - φg (baseKA l).ρ) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom (baseKA l).ρ)) e1
    have e3 := Scheme.preimage_basicOpen_top t (φf (baseKA l).ρ - φg (baseKA l).ρ)
    rw [e2, Scheme.basicOpen_zero] at e3
    obtain ⟨q⟩ : Nonempty ↥(Spec (d.Xo₂.X.residueField p)) := ⟨IsLocalRing.closedPoint _⟩
    have hq : q ∈ t ⁻¹ᵁ d.Xo₂.X.basicOpen (φf (baseKA l).ρ - φg (baseKA l).ρ) := by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hp
    rw [e3] at hq
    simp at hq
  have hφ : φf = φg := by
    apply ringHom_KA_ext_of_A_eq_one hA
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro p hp
    exact (key p hp).elim
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ f.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ g.appTop := CommRingCat.hom_ext hφ
  rw [cancel_epi] at h1
  rw [← cancel_mono (Sp (KA l)).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h1]

theorem coe_incl {S T : IntermediateField ℚ ℂ} (h : S ≤ T) (t : S) :
    (((IntermediateField.inclusion h).toRingHom t : T) : ℂ) = (t : ℂ) := rfl

theorem eq_incl {S T : IntermediateField ℚ ℂ} (h : S ≤ T) (j : S →+* T) (hj : ∀ t, ((j t : T) : ℂ) = (t : ℂ)) :
    j = (IntermediateField.inclusion h).toRingHom := by
  exact RingHom.ext fun t => Subtype.ext ((hj t).trans (coe_incl h t).symm)

end

end GlobalTheory.ClsVal.Cmp
