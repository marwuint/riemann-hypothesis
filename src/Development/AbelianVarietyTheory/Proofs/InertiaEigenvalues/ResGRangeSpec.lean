import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob.ResRange

variable (Ω K L : Type) [Field Ω] [Field K] [Algebra K Ω] [Field L] [Algebra L Ω] [Algebra K L]
  [IsScalarTower K L Ω]

theorem resG_apply (τ : G L Ω) (z : Ω) : resG K L Ω τ z = τ z := rfl

def embAction : MulAction (G K Ω) (L →ₐ[K] Ω) where
  smul σ φ := (σ : Ω →ₐ[K] Ω).comp φ
  one_smul φ := by ext; rfl
  mul_smul σ τ φ := by ext; rfl

attribute [local instance] embAction

end GlobalTheory.DelGlob.ResRange

namespace GlobalTheory.DelGlob.ResRange

end GlobalTheory.DelGlob.ResRange

namespace GlobalTheory.DelGlob

end GlobalTheory.DelGlob
