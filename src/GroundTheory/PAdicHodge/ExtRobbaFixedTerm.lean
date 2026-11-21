import Mathlib
import GroundTheory.PAdicHodge.DMTeichBasic
import GroundTheory.PAdicHodge.DMTeichPow
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

abbrev πB : T.B := algebraMap Γ T.B T.π

def DigLe (x : Γ) (Θ : ℝ) : Prop := ∀ n, ‖T.coeff x n‖ ≤ Θ

variable {T}

theorem digLe_one_of_mem_int {x : Γ} (hx : x ∈ T.int) : T.DigLe x 1 := T.mem_int_iff.1 hx

theorem DigLe.convergesAt {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ConvergesAt (T.zcoeff x) r :=
  T.convergesAt_of_forall_weight_le (ρ := 1) (Y := Θ) hr0 hr1 fun n => by
    rw [one_pow, mul_one]; exact hx n

theorem DigLe.convAll {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) : T.ConvAll (algebraMap Γ T.B x) :=
  fun _ hr0 hr1 => by rw [T.coeffB_algebraMap]; exact hx.convergesAt hr0 hr1

theorem convAll_algebraMap_of_mem_int {U : Γ} (hU : U ∈ T.int) :
    T.ConvAll (algebraMap Γ T.B U) := (digLe_one_of_mem_int hU).convAll

namespace TeichFrob

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
