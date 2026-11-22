import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RHof
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.NmK
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def galS (M : Model l K) (g : K.fixingSubgroup) (n j : ℕ) : M.Hc false n j →ₛₗ[(per l K).σA g] M.Hc false n j :=
  B.galHc (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K g) (galOC_okToOC _) false n j

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K)

def nmGA : NMor L.γ M.p (κA (OK l K) L.I) L.γ M.p (κA (OK l K) L.I) (L.σA g) :=
  nmK L.γ L.γ M.p M.p (L.σA g) (hL.σ_dp g) (hL.σ_O g) (𝟙 _) (Category.id_comp _)

def nmGB : NMor L.γB M.q (κA K L.IB) L.γB M.q (κA K L.IB) (L.σB g) :=
  nmK L.γB L.γB M.q M.q (L.σB g) (hL.σB_dp g) (hL.σB_K g) (𝟙 _) (Category.id_comp _)

variable (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

def homGal : Hom (chainOf hL M s hQ rH) (chainOf hL M s hQ rH) where
  sΛ := (per l K).σA g
  sA := L.σA g
  sB := L.σB g
  fS n j := galS M g n j
  fZn n j := nmHM (nmGA hL g M) l s none n j
  fZ j := nmHO (nmGA hL g M) l s j
  fW j := nmHO (nmGB hL g M) 1 s j
  fV _ := LinearMap.id

def GalRed : Prop :=
  ∀ n j (x : M.Hc false n j), nmHM (nmGA hL g M) l s none n j (rH n j x) = rH n j (galS M g n j x)

end

end CrystallineSemistableComparison.Pb.Kap
