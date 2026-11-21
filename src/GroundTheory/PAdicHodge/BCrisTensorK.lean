import Mathlib
import GroundTheory.PAdicHodge.BCrisNewton

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

section MaxUnramified

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

instance algebraMaxUnramified : Algebra (maxUnramified p K) K :=
  (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).toRingHom.toAlgebra

theorem coe_algebraMap_maxUnramified (k : maxUnramified p K) :
    ((algebraMap (maxUnramified p K) K k : K) : PadicAlgCl p) = k :=
  rfl

instance isScalarTower_maxUnramified_algCl :
    IsScalarTower (maxUnramified p K) K (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_padic_maxUnramified :
    IsScalarTower ℚ_[p] (maxUnramified p K) K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance finiteDimensional_maxUnramified [FiniteDimensional ℚ_[p] K] :
    FiniteDimensional (maxUnramified p K) K :=
  Module.Finite.of_restrictScalars_finite ℚ_[p] (maxUnramified p K) K

def unramifiedOver : IntermediateField (maxUnramified p K) (PadicAlgCl p) :=
  IntermediateField.extendScalars (inf_le_right : maxUnramified p K ≤ unramifiedClosure p)

theorem mem_unramifiedOver {x : PadicAlgCl p} : x ∈ unramifiedOver K ↔ x ∈ unramifiedClosure p :=
  Iff.rfl

instance isAlgClosure_maxUnramified : IsAlgClosure (maxUnramified p K) (PadicAlgCl p) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) (maxUnramified p K)⟩

instance normal_unramifiedOver : Normal (maxUnramified p K) (unramifiedOver K) := by
  refine IntermediateField.normal_iff_forall_map_le'.2 fun σ x hx => ?_
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  exact gal_mem_unramifiedClosure (σ.restrictScalars ℚ_[p]) hy

end MaxUnramified

namespace ACris

open scoped TensorProduct

section Tensor

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def unramifiedToBCrisPlus : unramifiedClosure p →ₐ[ℚ_[p]] BCrisPlus ℂ_[p] p :=
  ((AlgEquiv.ofInjective (iotaPlusAlg (p := p))
      fun _ _ h => iotaPlus_injective (K := ℂ_[p]) (p := p) h).symm :
      (iotaPlusAlg (p := p)).range →ₐ[ℚ_[p]] BCrisPlus ℂ_[p] p).comp
    (((algClToBdR p).comp (unramifiedClosure p).val).codRestrict _ fun u => unramifiedClosure_le u.2)

instance algebraMaxUnramifiedBCrisPlus : Algebra (maxUnramified p K) (BCrisPlus ℂ_[p] p) :=
  (unramifiedToBCrisPlus.comp (IntermediateField.inclusion
    (inf_le_right : maxUnramified p K ≤ unramifiedClosure p))).toRingHom.toAlgebra

instance moduleMaxUnramifiedBCrisPlus : Module (maxUnramified p K) (BCrisPlus ℂ_[p] p) :=
  Algebra.toModule

instance algebraMaxUnramifiedBdRPlus : Algebra (maxUnramified p K) 𝔹 :=
  ((algClToBdR p).comp (maxUnramified p K).val).toRingHom.toAlgebra

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

variable [FiniteDimensional ℚ_[p] K]

end Tensor

end ACris

end GroundTheory.PAdicHodge
