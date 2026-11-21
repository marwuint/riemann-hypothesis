import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionOfBaseChangeFieldExt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibreImm

set_option backward.isDefEq.respectTransparency.types false

theorem isPullback_pullback_map {S S' : Scheme.{0}} (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y) :
    IsPullback ((Over.pullback a).map v).left (pullback.fst X.hom a) (pullback.fst Y.hom a) v.left := by
  have h1 : ((Over.pullback a).map v).left ≫ pullback.fst Y.hom a = pullback.fst X.hom a ≫ v.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback a).map v).left ≫ pullback.snd Y.hom a = pullback.snd X.hom a :=
    Over.w ((Over.pullback a).map v)
  refine IsPullback.of_right ?_ h1 (IsPullback.of_hasPullback Y.hom a).flip
  have h := (IsPullback.of_hasPullback X.hom a).flip
  rw [h2, Over.w v]
  exact h

theorem closedImm_comp_iff {S S' S'' : Scheme.{0}} (b : S'' ⟶ S') (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y) :
    IsClosedImmersion ((Over.pullback (b ≫ a)).map v).left ↔
      IsClosedImmersion ((Over.pullback b).map ((Over.pullback a).map v)).left := by
  let e := Over.pullbackComp b a
  exact MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk ((Over.forget _).mapIso (e.app X)) ((Over.forget _).mapIso (e.app Y))
      (congrArg (·.left) (e.hom.naturality v).symm))

theorem closedImm_pullback {S S' : Scheme.{0}} (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y)
    (h : IsClosedImmersion v.left) : IsClosedImmersion ((Over.pullback a).map v).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_pullback_map a v).flip h

theorem closedImm_of_pullback {k Ω : CommRingCat.{0}} (hk : IsField k) (hΩ : IsField Ω) (φ : k ⟶ Ω)
    {X Y : Over (Spec k)} (v : X ⟶ Y)
    (h : IsClosedImmersion ((Over.pullback (Spec.map φ)).map v).left) : IsClosedImmersion v.left := by
  letI := hk.toField
  letI := hΩ.toField
  letI := φ.hom.toAlgebra
  have hd := GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_descendsAlong_fpqc
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map φ) :=
    GlobalTheory.ClosedImmFieldDescent.fpqc_specMap_field k Ω
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (isPullback_pullback_map _ v)
    (MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (IsPullback.of_hasPullback Y.hom (Spec.map φ)).flip hq) h

theorem closedImm_iff_residue {W : Scheme.{0}} {X Y : Over W} (v : X ⟶ Y) (k : Type) [Field k] (w : Sp k ⟶ W) :
    IsClosedImmersion ((Over.pullback w).map v).left ↔
      IsClosedImmersion ((Over.pullback (W.fromSpecResidueField (w (IsLocalRing.closedPoint k)))).map v).left := by
  conv_lhs => rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k W w]
  rw [closedImm_comp_iff]
  exact ⟨closedImm_of_pullback (Field.toIsField _) (Field.toIsField _) _ _, closedImm_pullback _ _⟩

end GlobalTheory.TorusFibreImm

end
