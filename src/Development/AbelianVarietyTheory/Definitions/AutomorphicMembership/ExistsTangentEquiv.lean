import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCohSubDegEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.Points
open GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.LocM

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {T T' : X.Opens}

def affPt (hT : IsAffineOpen T) : Sp Γ(X, T) ⟶ X := hT.fromSpec

theorem le_preimage_affPt (hT : IsAffineOpen T) : ⊤ ≤ affPt hT ⁻¹ᵁ T := hT.fromSpec_preimage_self.ge

theorem valR_affPt (hT : IsAffineOpen T) (a : Γ(X, T)) : valR (affPt hT) T a = a := by
  have h := valMap_specMap_fromSpec hT (C := Γ(X, T)) (𝟙 _) (le_preimage_specMap_fromSpec hT _)
  have e : Spec.map (𝟙 (CommRingCat.of Γ(X, T))) ≫ hT.fromSpec = affPt hT := by
    rw [Spec.map_id]
    exact Category.id_comp _
  rw [← e]
  exact (valR_eq _ _ (le_preimage_specMap_fromSpec hT (C := Γ(X, T)) (𝟙 _)) a).trans congr(($h).hom a)

theorem spMap_affPt (hT : IsAffineOpen T) (hT' : IsAffineOpen T') (h : T' ≤ T) :
    spMap (resG X h) ≫ affPt hT = affPt hT' := hT.map_fromSpec hT' _

def CoordOpen (T : X.Opens) : Prop :=
  IsAffineOpen T ∧ ∃ (W : t.G.left.Opens) (h : T ≤ unitSec t.G ⁻¹ᵁ W) (n : ℕ) (f : Fin n → Γ(t.G.left, W)),
    VB.IsFrame fun b => dUnit t.G h (f b)

theorem exists_coordOpen {V : X.Opens} {x : X} (hx : x ∈ V) : ∃ T, CoordOpen t T ∧ x ∈ T ∧ T ≤ V := by
  have := t.semi
  have := t.semi.smooth
  obtain ⟨U, n, s, hU, hs⟩ := exists_isFrame_omega t.G x
  obtain ⟨T, W, hT, hle, c⟩ := Conormal.exists_isChart (sec_hom η[t.G]) (V := V ⊓ U) ⟨hx, hU⟩
  choose f hf using fun b => c.d_surjective (sec_hom η[t.G]) (resM (omega t.G) (hle.trans inf_le_right) (s b))
  exact ⟨T, ⟨c.affine_base, W, c.le, n, f, (funext hf :) ▸ hs.res (hle.trans inf_le_right)⟩, hT, hle.trans inf_le_left⟩

variable {t}

theorem CoordOpen.mono (h : CoordOpen t T) (hT' : IsAffineOpen T') (e : T' ≤ T) : CoordOpen t T' := by
  obtain ⟨-, W, hW, n, f, hf⟩ := h
  exact ⟨hT', W, e.trans hW, n, f, by simpa only [resM_dUnit] using hf.res e⟩

theorem tanEv_dUnit_eq {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (h : ⊤ ≤ x ⁻¹ᵁ T) {W : t.G.left.Opens} (hW : T ≤ unitSec t.G ⁻¹ᵁ W) (f : Γ(t.G.left, W)) :
    ⊤ ≤ v ⁻¹ᵁ W ∧ tanEv t hv h (dUnit t.G hW f) = (valR v W f).snd := by
  have hv' : ⊤ ≤ v ⁻¹ᵁ W := fun z _ => by
    obtain ⟨s, rfl⟩ := surjective_sec_epsZero z
    have h₁ : s ∈ (x ≫ unitSec t.G) ⁻¹ᵁ W := hW (h trivial)
    rw [← epsZero_comp_of_isTanAtG t hv] at h₁
    exact h₁
  exact ⟨hv', (tanEv_dUnit t hv h hW hv' f).trans (congrArg TrivSqZeroExt.snd (valR_eq v W hv' f).symm)⟩

def IsSecOf (hT : IsAffineOpen T) (v : TanM (affPt hT) t.G) (l : Γ(Lie t.G, T)) : Prop :=
  ∀ s : Γ(omega t.G, T), dualApp l le_rfl s = tanEv t (isTan_tv v) (le_preimage_affPt hT) s

theorem CoordOpen.exists_equiv (h : CoordOpen t T) :
    ∃ Θ : TanM (affPt h.1) t.G ≃ₗ[Γ(X, T)] Γ(Lie t.G, T), ∀ v, IsSecOf h.1 v (Θ v) := by
  obtain ⟨hT, W, hW, n, f, hf⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LocM.TanPair.exists_tanM_equiv E H X t _ (affPt hT) T (le_preimage_affPt hT) n _ hf
  refine ⟨Φ ≪≫ₗ (hf.dual.basis le_rfl).equivFun.symm, fun v s => ?_⟩
  let ev : Γ(omega t.G, T) →ₗ[Γ(X, T)] Γ(X, T) :=
    { toFun := tanEv t (isTan_tv v) (le_preimage_affPt hT)
      map_add' := tanEv_add t _ _
      map_smul' := fun a s => (tanEv_smul t _ _ a s).trans
        (congrArg (· * _) ((valR_eq _ _ (le_preimage_affPt hT) a).symm.trans (valR_affPt hT a))) }
  refine LinearMap.congr_fun (g := ev) ((hf.basis le_rfl).ext fun b => ?_) s
  rw [IsFrame.basis_apply, ← hf.dual_basis_repr le_rfl, resM_self, LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply, hΦ]
  rfl

theorem IsSecOf.eq_resM (h : CoordOpen t T) {hT' : IsAffineOpen T'} (e : T' ≤ T) {v : TanM (affPt h.1) t.G}
    {v' : TanM (affPt hT') t.G} {l : Γ(Lie t.G, T)} {l' : Γ(Lie t.G, T')} (hl : IsSecOf h.1 v l) (hl' : IsSecOf hT' v' l')
    (hv : (tv v').left = spMap (dualMap (resG X e)) ≫ (tv v).left) : l' = resM _ e l := by
  obtain ⟨hT, W, hW, n, f, hf⟩ := h
  refine hf.dual_ext e fun b => ?_
  obtain ⟨h₁, h₂⟩ := tanEv_dUnit_eq (isTan_tv v) (le_preimage_affPt hT) hW (f b)
  rw [hl', dualApp_res, dualApp_resM l le_rfl e, hl, h₂, resM_dUnit, (tanEv_dUnit_eq _ _ _ _).2, hv,
    valR_spMap_comp _ _ _ h₁]
  simp [Formalism.L2.Pj.dualMap]

theorem exists_tangent_equiv {C : Scheme.{0}} {t' : SAB H C} {g : C ⟶ X} (m : SABMap t' t g) :
    ∃ Ψ : ∀ (T : C.Opens) (h : CoordOpen t' T) (x : Sp Γ(C, T) ⟶ X), affPt h.1 ≫ g = x →
      (TanM x t.G ≃ₗ[Γ(C, T)] Γ(Lie t'.G, T)),
      ∀ T h x hx T' h' x' hx' (e : T' ≤ T) u u', (tv u').left = spMap (dualMap (resG C e)) ≫ (tv u).left →
        Ψ T' h' x' hx' u' = resM _ e (Ψ T h x hx u) := by
  choose Θ hΘ using fun T (h : CoordOpen t' T) => h.exists_equiv
  refine ⟨fun T h x hx => (pushE m _ hx).symm ≪≫ₗ Θ T h, fun T h x hx T' h' x' hx' e u u' hu => ?_⟩
  obtain ⟨v, rfl⟩ := (pushE m _ hx).surjective u
  obtain rfl : pushE m _ hx' (tanOf (isTan_map _ (spMap_affPt h.1 h'.1 e) (isTan_tv v))) = u' :=
    tan_ext (by rw [hu, left_pushE, left_pushE, left_tanOf, Category.assoc])
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (hΘ T h v).eq_resM h e (hΘ T' h' _) rfl

end Sections

section Inhabitants

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem Mdl.exists_point (h1 : 1 ≤ Dw.p + Dw.q) (Z : Mdl Y i₀) {k : Type} [Field k] [IsAlgClosed k]
    (φ : Z.i.c.V W →+* k) : ∃ x : Sp k ⟶ Z.X, x ≫ Z.s = spMap φ := by
  have := SharedLaws.isProper_toroidalModel_structureMap Z
  have := Z.flat
  obtain ⟨z⟩ := SharedLaws.nonempty_model h1 Z
  have : Surjective Z.s := ⟨fun y => by
    have h₀ : IsLocalRing.closedPoint (Z.i.c.V W) ∈ Set.range Z.s :=
      (IsLocalRing.specializes_closedPoint (Z.s z)).mem_closed Z.s.isClosedMap.isClosed_range ⟨z, rfl⟩
    exact (Flat.generalizingMap Z.s).stableUnderGeneralization_range (IsLocalRing.specializes_closedPoint y) h₀⟩
  let f := pullback.snd Z.s (spMap φ)
  have : CompactSpace ↥(pullback Z.s (spMap φ)) := QuasiCompact.compactSpace_of_compactSpace f
  have : Nonempty ↥(pullback Z.s (spMap φ)) := f.surjective.nonempty
  obtain ⟨y, -, hy⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback Z.s (spMap φ))) Set.univ_nonempty
  exact ⟨pointOfClosedPoint f y hy ≫ pullback.fst _ _, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]⟩

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

instance At.nonempty_crv (ct : At S κ p) : Nonempty ct.Crv := by
  have := Fact.mk ct.hp
  have := ct.YY.i.c.fin
  have : NumberField ct.YY.i.c.F := NumberField.mk
  have hV := SharedLaws.mem_nonunits_V ct.YY.i.c ct.hp.ne_zero ct.hW
  obtain ⟨-, h₂⟩ := GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField (ct.YY.i.c.V ct.W) ct.hp.ne_zero hV
  have : CharP (IsLocalRing.ResidueField (ct.YY.i.c.V ct.W)) p := (CharP.charP_iff_prime_eq_zero ct.hp).2 (by
    rw [← map_natCast (IsLocalRing.residue _), IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hV)
  letI := ZMod.algebra (IsLocalRing.ResidueField (ct.YY.i.c.V ct.W)) p
  letI := ZMod.algebra ct.Fbar p
  let ψ : IsLocalRing.ResidueField (ct.YY.i.c.V ct.W) →ₐ[ZMod p] ct.Fbar := IsAlgClosed.lift
  obtain ⟨x, -⟩ := ct.YY.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge))
    (ψ.toRingHom.comp (IsLocalRing.residue _))
  exact Curve.nonempty_of_point x

instance At.nonempty_crvQ (ct : At S κ p) : Nonempty ct.CrvQ := by
  have := ct.YY.i.c.fin
  let ψ : ct.YY.i.c.F →ₐ[ℚ] AlgebraicClosure κ.c.F := IsAlgClosed.lift
  obtain ⟨x, -⟩ := ct.YY.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge))
    (ψ.toRingHom.comp (ct.YY.i.c.V ct.W).subtype)
  exact Curve.nonempty_of_point x

end Inhabitants

namespace Curve

end Curve

namespace At

end At

end GlobalTheory.LocM
