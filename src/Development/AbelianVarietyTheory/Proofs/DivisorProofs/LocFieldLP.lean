import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan

noncomputable section

namespace GlobalTheory.ThK.LiftPair

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldLP (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

end GlobalTheory.ThK.LiftPair

end
