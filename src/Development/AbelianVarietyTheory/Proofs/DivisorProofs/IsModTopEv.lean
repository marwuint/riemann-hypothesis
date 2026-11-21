import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweAdelic
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweNonsplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance isModTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

end GlobalTheory.HoweNonsplit
