import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PointDataQ
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteSublevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtGermCompare

theorem surjective_cube {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
  have hG := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have s₂ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg G) s₁
  rw [Over.w (snd G G)] at s₂
  have s₃ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg (G ⊗ G)) s₂
  rw [Over.w (snd G (G ⊗ G))] at s₃
  exact s₃

theorem cubical_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have h : c.t.s = c'.t.s := JetSer.gen_ext_val L.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen fun y J hJ =>
    gen_unique L.isLB (φ := thφ G (x3 G)) (ε := thε) (G3 G).hom e.left (Over.w e) sj c.isGen c'.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm) _ _ y J hJ
  obtain ⟨⟨t⟩, _⟩ := c
  obtain ⟨⟨t'⟩, _⟩ := c'
  obtain rfl : t = t' := h
  rfl

open GlobalTheory.FamGerm GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData

end GlobalTheory.PtGermCompare
