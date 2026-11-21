import Mathlib
import GroundTheory.Brauer.CrossedProduct
import GroundTheory.Brauer.CrossedProductSimple
import GroundTheory.Brauer.CrossedProductMaps
import GroundTheory.Brauer.CrossedProductInj
import GroundTheory.Brauer.CrossedProductTensor
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
import GroundTheory.Brauer.BaseChange
import GroundTheory.Brauer.MulDistribMulActionQuotientFixedPoints
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open groupCohomology

universe u

namespace CrossedProduct

section Inflate

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]

theorem algebraMap_restrictNormalHom (σ : L' ≃ₐ[K] L') (x : L) :
    algebraMap L L' (AlgEquiv.restrictNormalHom L σ x) = σ (algebraMap L L' x) :=
  AlgEquiv.restrictNormal_commutes σ L x

theorem unitsMap_smul (σ : L' ≃ₐ[K] L') (m : Lˣ) :
    Units.map (algebraMap L L' : L →* L') (AlgEquiv.restrictNormalHom L σ • m) =
      σ • Units.map (algebraMap L L' : L →* L') m := by
  ext
  exact algebraMap_restrictNormalHom σ (m : L)

variable (L') in

def inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L') → L'ˣ :=
  fun p => Units.map (algebraMap L L' : L →* L')
    (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))

theorem val_inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L')) :
    ((inflate L' f p : L'ˣ) : L') =
      algebraMap L L' (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2)) :=
  rfl

variable (L') in

theorem isMulCocycle₂_inflate {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (inflate L' f) :=
  (H2mul.mapCocycles₂ (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    unitsMap_smul ⟨f, hf⟩).2

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L L')
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

def inflateIncl : L' →ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  (incl : L →ₐ[K] CrossedProduct hf).mapMatrix.comp ((Algebra.leftMulMatrix b).restrictScalars K)

omit [Normal K L] in
theorem inflateIncl_apply (a : L') :
    inflateIncl b hf a = (Algebra.leftMulMatrix b a).map incl :=
  rfl

variable [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K L'] [IsGalois K L']
  [Nonempty ι]

end Matrix

end Inflate

end CrossedProduct

namespace BrauerGroup

end BrauerGroup

namespace H2mul

section Inflation

variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]

def inflation : H2mul (L ≃ₐ[K] L) Lˣ →* H2mul (L' ≃ₐ[K] L') L'ˣ :=
  mapPair (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    CrossedProduct.unitsMap_smul

variable {K L L'}

theorem inflation_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    inflation K L L' (mk _ _ c) =
      mk _ _ ⟨CrossedProduct.inflate L' (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ),
        CrossedProduct.isMulCocycle₂_inflate L' c.2⟩ :=
  rfl

end Inflation

end H2mul

end GroundTheory.Brauer

end
