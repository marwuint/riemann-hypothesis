import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory.PolModLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coe_OF (a : OF E) : (((a : maximalRealSubfield E)) : E) = algebraMap (OF E) E a := rfl

end GlobalTheory.PolModLattice

