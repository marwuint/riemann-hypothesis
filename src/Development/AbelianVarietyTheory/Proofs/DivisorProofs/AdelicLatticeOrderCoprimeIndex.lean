import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatrices

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.LatLoc

variable {E : Type} [Field E] [NumberField E]

theorem natCast_coord (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (n : Af E) w = (n : w.adicCompletion E) := by
  rfl

end GlobalTheory.CMVal.LatLoc
