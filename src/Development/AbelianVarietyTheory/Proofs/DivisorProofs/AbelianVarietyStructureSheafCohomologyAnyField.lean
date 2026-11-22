import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1RankDescendsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveAxesDescendField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyDescendsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelian_HO_field_any : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧
      Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  intro K _ A _ g hab hsm
  let L := AlgebraicClosure K
  let σ : K →+* L := algebraMap K L
  have hpb : IsPullback (pullback.fst A.hom (spMap σ)) (pullback.snd A.hom (spMap σ)) A.hom (spMap σ) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨inst, hgp, habB, hsmB⟩ := _root_.GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback K L σ A _ _ _ hpb
  have hB := @_root_.GlobalTheory.AbCoh.structureSheafCoh_abelianVariety_algClosed L _ _ (Over.mk (pullback.snd A.hom (spMap σ))) inst g (habB hab) (hsmB g hsm)
  obtain ⟨hfin, hrk, hw, hnp, hax⟩ := hB
  obtain ⟨hfinA, hrkA⟩ := @_root_.GlobalTheory.AbCoh.finrank_HO1_descend_field K L _ _ _ A _ _ inst _ hgp hab g hfin hrk
  obtain ⟨hnpA, haxA⟩ := @_root_.GlobalTheory.AbCoh.noPrimO2_axesO1_descend K L _ _ _ A _ _ inst _ hgp hab
  exact ⟨hfinA, hrkA, @_root_.GlobalTheory.AbCoh.wedgeO_descends_field K L _ _ _ A _ _ inst _ hgp hab hw, hnpA hnp, haxA hax⟩

end GlobalTheory.AbCoh
