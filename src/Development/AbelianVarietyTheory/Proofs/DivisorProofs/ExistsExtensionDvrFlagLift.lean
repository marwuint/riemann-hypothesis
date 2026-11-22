import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifTrait

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1000000 in

theorem exists_intFr_frBor (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
    (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt) (hzs : z ≫ pullback.snd _ _ = spMap io) :
    letI := io.toAlgebra
    ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1 := by
  let _ := io.toAlgebra
  intro y₀ hy0
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T io O β Y yt z hz hzs _ m
  have hx : (z ≫ pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨x₀, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ := y₀
  change x₀ = z ≫ pullback.fst _ _ at hy0
  subst hy0
  obtain ⟨ub, u, hub, htan, heig, hbas, htri⟩ := lieFree Xo c T io _ t' _ m1 m2 hx u₀ htan₀ heig₀ hbas₀
  obtain ⟨θ, s, hθ, hmatch, hgen, a, ha⟩ :=
    GlobalTheory.DepthSum.thetaFrame_trait Xo c T io O β Y yt z hz hzs _ m t' m1 m2 s₀ hgen₀
  let y : FrPt Xo c T.Fr := ⟨z ≫ pullback.fst _ _, hx, u, htan, heig, hbas, s, hgen⟩
  choose cf hcf using htri
  let tt : Ix Dw → T.Frˣ := fun o => match o with
    | none => a
    | some p => (hcf p.1 p.2).1.unit
  have hFB : FrBor tt ⟨z ≫ pullback.fst _ _, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ y := by
    refine ⟨rfl, fun τ i => ⟨cf τ i, (hcf τ i).1.unit_spec.symm, (hcf τ i).2.1, (hcf τ i).2.2⟩, 𝟙 _,
      Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    change (Scheme.Hom.appLE (𝟙 (Gx (z ≫ pullback.fst _ _))) _ _ h).hom
      (scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i) = s.f i
    rw [ha i, Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp, show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨⟨y, GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T.Fr y, _, t', m1, m2, ⟨ub, hub⟩, θ, hθ, hmatch⟩, tt, hFB⟩

end Frames

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

section Split

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem charZero_residue_of_map {K : Type} [Field K] [CharZero K] (V : Type) [CommRing V] [IsLocalRing V]
    (f : Sp V ⟶ Sp K) : CharZero (ResidueField V) :=
  charZero_of_injective_ringHom ((residue V).comp (Spec.preimage f).hom).injective

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, Sx, ⟨d⟩⟩ := GlobalTheory.UnifAfterExt.exists_finite_split _ h₀
  have : Algebra.IsSeparable (ResidueField W) k' := inferInstance
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, -, -, e, he⟩ := GlobalTheory.unramExt W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) Sx _ d)⟩

end Split

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

end GlobalTheory.UnifTrait
