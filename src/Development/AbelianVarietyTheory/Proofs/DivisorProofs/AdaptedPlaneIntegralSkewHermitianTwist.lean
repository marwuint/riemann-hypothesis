import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section
namespace GlobalTheory.CtLeviCont
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance topRingAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
instance borelUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
end GlobalTheory.CtLeviCont
