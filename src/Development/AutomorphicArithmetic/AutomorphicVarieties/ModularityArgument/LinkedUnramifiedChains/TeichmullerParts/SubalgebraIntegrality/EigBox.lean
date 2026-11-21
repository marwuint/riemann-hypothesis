import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

section Lin

variable {W W₂ Z Z₂ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W₂] [Module ℂ W₂]
  [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z₂] [Module ℂ Z₂]

private def sl (l : Z →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] W :=
  (TensorProduct.rid ℂ W).toLinearMap ∘ₗ LinearMap.lTensor W l

end Lin

end UpperTheory.V.Z.J.D
