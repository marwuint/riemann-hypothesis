import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBaseStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndexStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInvStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacterStatement

namespace GlobalTheory.Proof.cm_localDensities_productFormula

theorem densityProduct : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct :=
  fun F E _ _ _ _ _ _ σ h₁ h₂ h₃ =>
    ⟨GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base F E σ h₁ h₂ h₃, GlobalTheory.T.dual_lattice_different_index F E σ h₁ h₂ h₃, _root_.GlobalTheory.LocalDifferentProduct.prod_normDifferentV F E σ h₁ h₂ h₃,
      _root_.GlobalTheory.AdelicCharDilate.exists_eq_std_dilate F E σ h₁ h₂ h₃, GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv F E σ h₁ h₂ h₃, GlobalTheory.T.product_localDensities_adeleCharacter F E σ h₁ h₂ h₃⟩

end GlobalTheory.Proof.cm_localDensities_productFormula
