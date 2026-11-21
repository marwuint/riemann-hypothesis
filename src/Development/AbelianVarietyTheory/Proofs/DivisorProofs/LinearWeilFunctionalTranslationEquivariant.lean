import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {Y : Spc F E n} (g h : UA σ Y.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {Y : Spc F E n} : mat (1 : UA σ Y.J) = 1 := rfl

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

noncomputable section

def cmpGL {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) : GL (Fin n) (Fv F v) :=
  Units.map (piW t).mapMatrix.toMonoidHom h.1

theorem cmpGL_val {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) :
    (cmpGL t h).1 = (mat h).map (piW t) := rfl

end

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

end GlobalTheory.LocalUnitSubgroupClosure
