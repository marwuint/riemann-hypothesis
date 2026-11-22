import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TruncFix

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idem (T : Finset (Pl F)) : AF F := ∑ v ∈ T, GlobalTheory.LatVac.liftV v 1

theorem evFin_liftV_one (v w : Pl F) : evFin F w (GlobalTheory.LatVac.liftV v 1) = if w = v then 1 else 0 := by
  by_cases h : w = v
  · subst h; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
  · rw [if_neg h]; exact GlobalTheory.ThK.LocalOps.evFin_of_at h (GlobalTheory.LatVac.at_liftV v 1)

theorem evFin_idem (T : Finset (Pl F)) (w : Pl F) : evFin F w (idem T) = if w ∈ T then 1 else 0 := by
  classical
  simp only [idem, map_sum, evFin_liftV_one]
  rw [Finset.sum_ite_eq]

theorem idem_mul_idem (T : Finset (Pl F)) : idem T * idem T = idem T := by
  classical
  conv_lhs => rw [idem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, ← idem, evFin_idem, if_pos hv]

variable {σ : E →ₐ[F] E}

end GlobalTheory.TruncFix
