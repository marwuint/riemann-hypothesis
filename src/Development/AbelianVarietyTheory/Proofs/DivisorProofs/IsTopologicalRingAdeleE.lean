import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance isTopologicalRing_adeleE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

instance t2Space_adeles_E : T2Space (AE F E) :=
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

instance borelSpace_adelicU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem incM_dblGram : incM F (dblGram finSumFinEquiv J) = dblGram finSumFinEquiv (incM F J) := by
  rw [incM, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]; rfl

end GlobalTheory.DefDoubling
