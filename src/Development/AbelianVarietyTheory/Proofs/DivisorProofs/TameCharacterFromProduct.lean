import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdeal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare.TameConj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (idealHat CongMod)
open GlobalTheory.IdemSupport (mem_intAE_iff parts_cA finPart_cA_mem)

variable {D : D7}

theorem mul_mem_intAE {y z : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) (hz : z ∈ intAE D) :
    y * z ∈ intAE D := by
  rw [mem_intAE_iff] at hy hz ⊢
  rw [RingHom.map_mul]
  exact mul_mem hy hz

theorem FinUnit_mul {x y : (AE D)ˣ} (hx : FinUnit x) (hy : FinUnit y) : FinUnit (x * y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]
  · rw [Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.1 hy.2.1
  · rw [mul_inv, Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.2 hy.2.2

theorem FinUnit_inv {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit x⁻¹ := by
  refine ⟨?_, hx.2.2, hx.2.1⟩
  have e : infPart D (x : AE D) * infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rwa [hx.1, one_mul] at e

theorem FinUnit_conj {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit (Units.map (cA D).toMonoidHom x) := by
  refine ⟨?_, finPart_cA_mem hx.2.1, finPart_cA_mem hx.2.2⟩
  exact (parts_cA (x : AE D)).1.trans (by rw [hx.1, RingHom.map_one])

end GlobalTheory.GeoActCompare.TameConj
