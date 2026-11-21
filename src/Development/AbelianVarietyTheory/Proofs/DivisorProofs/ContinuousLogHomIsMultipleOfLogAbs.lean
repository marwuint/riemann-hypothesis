import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import GroundTheory.GlobalFields.Adele.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

open scoped GroundTheory.Global.AdeleBaseChange NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.IdeleLogHom

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

section Transfer

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toE : (AE F E)ˣ →* IdeleGroup E :=
  Units.map (adeleTensorAlgEquivLeft F E : AE F E →ₐ[AF F] AdeleRing (𝓞 E) E).toMonoidHom

theorem absE_eq_ideleModule (x : (AE F E)ˣ) :
    (absE F E x : ℝ) = (IdeleGroup.ideleModule E (toE F E x) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), ← GlobalTheory.ModuAdele.modu_norm_eq_absE]
  have h2 : ∀ u : (AF F)ˣ, (((adeleClass F).modu u : ℝ≥0) : ℝ) = (IdeleGroup.ideleModule F u : ℝ) := fun u => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) u : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u
  have h3 : Units.map (Algebra.norm (AF F) : AE F E →* AF F) x = ideleNorm F E (toE F E x) := by
    ext
    simp [toE, ideleNorm, Algebra.norm_eq_of_algEquiv]
  rw [h2, h3]

end Transfer

end GlobalTheory.IdeleLogHom
