import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.LocTateInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)

theorem finite_FE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

attribute [local instance] finite_FE

def basisEv : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)

theorem isModuleTopology_Ev : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

def coordEv : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
  haveI := isModuleTopology_Ev (E := E) v
  { (basisEv v).equivFun.toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.symm.toLinearMap }

theorem isTopologicalRing_Ev : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens

theorem t2Space_Fv_tensor : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

theorem locallyCompactSpace_Ev : LocallyCompactSpace (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

theorem secondCountable_Ev : SecondCountableTopology (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isEmbedding.secondCountableTopology

theorem isOpenUnits_Ev : IsOpenUnits (Fv F v ⊗[F] E) :=
  haveI := isModuleTopology_Ev (E := E) v
  haveI := isTopologicalRing_Ev (E := E) v
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (basisEv v)

attribute [local instance] isTopologicalRing_Ev t2Space_Fv_tensor locallyCompactSpace_Ev secondCountable_Ev isOpenUnits_Ev

theorem distribHaarChar_Ev (u : (Fv F v ⊗[F] E)ˣ) :
    distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
  borelize (Fv F v ⊗[F] E)
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set b := basisEv (E := E) v
  set M := Algebra.leftMulMatrix b (u : Fv F v ⊗[F] E) with hMdef
  have hdet : M.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det b _).symm
  have hM : IsUnit M.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
  have hN0 : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hM).ne_zero
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
  have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (coordEv (E := E) v).symm (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : (((coordEv (E := E) v).symm.symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (coordEv (E := E) v).symm) =
      GlobalTheory.ModuNorm.mulUnitCE u := by
    ext x
    show b.equivFun.symm (Matrix.mulVec M (b.equivFun x)) = (u : Fv F v ⊗[F] E) * x
    rw [show Matrix.mulVec M (b.equivFun x) = b.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr b _ x,
      LinearEquiv.symm_apply_apply]
  rw [hext] at ht
  rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu,
    dif_pos (hdet ▸ hM)]
  convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN0 using 2
  exact Units.ext rfl

end GlobalTheory.LocTateInt

namespace GlobalTheory.LocTateInt

end GlobalTheory.LocTateInt
