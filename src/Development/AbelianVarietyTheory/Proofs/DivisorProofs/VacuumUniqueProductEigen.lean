import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.VacLine
open scoped Classical

namespace GlobalTheory.VacFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mem_SB_iff' {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ IsLocallyConstant f ∧ HasCompactSupport f := Iff.rfl

end GlobalTheory.VacFactor
