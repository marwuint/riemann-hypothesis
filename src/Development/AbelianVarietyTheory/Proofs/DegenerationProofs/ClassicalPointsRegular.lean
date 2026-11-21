import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  infer_instance

theorem flat_int_sections [CharZero Ω] (U : M.Z.Opens) : Module.Flat ℤ Γ(M.Z, U) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨n, hn⟩, ha⟩
  rw [Submodule.mem_bot]
  rcases (U : Set M.Z).eq_empty_or_nonempty with hU | hU
  · obtain rfl : U = ⊥ := SetLike.coe_injective hU
    exact Subsingleton.elim _ _
  · have h : n • M.res U hU a = 0 := by
      rw [← map_zsmul, show n • a = 0 from ha, map_zero]
    exact (map_eq_zero_iff _ (M.res_injective U hU)).1
      ((smul_eq_zero.1 h).resolve_left (nonZeroDivisors.ne_zero hn))

theorem flat_int [CharZero Ω] (π : M.Z ⟶ Sp ℤ) : Flat π := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : M.Z.affineOpens => U)
    (iSup_affineOpens_eq_top _) fun U => ?_
  have e : (π.appLE ⊤ U le_top).hom =
      (algebraMap ℤ Γ(M.Z, U)).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom := by
    have e' : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv ≫ π.appLE ⊤ U le_top).hom = algebraMap ℤ Γ(M.Z, U) :=
      RingHom.ext_int _ _
    rw [← e', ← CommRingCat.hom_comp, Iso.hom_inv_id_assoc]
  rw [e]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.bijective)
    (RingHom.flat_algebraMap_iff.2 (flat_int_sections M U))

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH.MinorModel

end GlobalTheory.ZH.MinorModel
