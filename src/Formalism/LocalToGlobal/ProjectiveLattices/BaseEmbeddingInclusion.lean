import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def extJ (σ : L →+* ℂ) (jK : M →ₛₗ[σ.comp (algebraMap K L)] W) : L ⊗[K] M →ₛₗ[σ] W :=
  letI : Module K W := Module.compHom W (σ.comp (algebraMap K L))
  let B : L →ₗ[K] M →ₗ[K] W := LinearMap.mk₂ K (fun a m => σ a • jK m)
    (fun a a' m => by rw [map_add, add_smul])
    (fun k a m => by
      show σ (k • a) • jK m = (σ (algebraMap K L k)) • (σ a • jK m)
      rw [Algebra.smul_def, map_mul, mul_smul])
    (fun a m m' => by rw [map_add, smul_add])
    (fun k a m => by
      show σ a • jK (k • m) = (σ (algebraMap K L k)) • (σ a • jK m)
      rw [map_smulₛₗ, RingHom.comp_apply, smul_comm])
  { toFun := TensorProduct.lift B
    map_add' := map_add _
    map_smul' := fun a x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        show σ (a • b) • jK m = σ a • (σ b • jK m)
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

def BaseEmbeddingInclusion (F : IntermediateField ℚ ℂ) [Algebra F LL] (σ₀ : LL →+* ℂ) : Prop :=
  ∀ x : F, σ₀ (algebraMap F LL x) = (x : ℂ)

end Forms

end Formalism.L2.Pj
