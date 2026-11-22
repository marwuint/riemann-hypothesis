import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMApprox
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.ExtRobbaNewton
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def ConvAll (b : T.B) : Prop := ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB b) ρ

variable {T}

theorem ConvAll.mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) : T.ConvAll (a * b) :=
  fun ρ h0 h1 => (T.convergesAt_coeffB_mul h0 h1 (ha ρ h0 h1) (hb ρ h0 h1)).1

theorem convAll_π_pow (c : ℕ) : T.ConvAll (algebraMap Γ T.B T.π ^ c) :=
  fun _ h0 _ => (gaussNorm_π_pow c h0).1

theorem convAll_zero : T.ConvAll (0 : T.B) := fun ρ _ _ => by
  rw [T.coeffB_zero_B]; exact convergesAt_zero

end TeichLift

namespace TeichLift

end TeichLift

namespace TeichLift

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

end TeichFrob

end TeichLift

namespace TeichLift

end TeichLift

namespace TeichLift

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

variable (T) in

def πTilde : T.RobbaTilde := T.edagToTilde ⟨algebraMap Γ T.B T.π, T.Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩
  (T.algebraMap_π_mem_Econ _)⟩

end TeichLift

end GroundTheory.PAdicHodge
