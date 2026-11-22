import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.GaussBridge

open GroundTheory.LocalField (valBall unitFiltrationUnits addCharConductor quasiCharConductor
  IsUnramifiedChar unifUnit unitsModRep unitsModFiltration unitsModCoset gaussSum)

local notation "ordF" => GroundTheory.LocalField.ord

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_isSmoothChar {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Continuous χ := by
  refine continuous_def.2 fun U _ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (χ.ker : Set Fˣ), fun y hy => ?_,
    hχ.preimage (continuous_const_mul _), by simp⟩
  have h : χ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  show χ y ∈ U
  rw [← h]
  exact hx

variable {χ : Fˣ →* ℂˣ} {ψ : AddChar F Circle}

end GlobalTheory.DelEps.GaussBridge

