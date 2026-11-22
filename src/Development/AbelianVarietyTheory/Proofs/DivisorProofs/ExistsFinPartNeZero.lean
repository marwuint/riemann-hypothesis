import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvZeroInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finPart (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ :=
  ∏ᶠ v, φ v fun i => evFin F v (x i)

theorem pure_eq_tens (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = tens (evI F) (⇑f) (finPart φ) := rfl

theorem snd_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h := congrArg Prod.snd (congrFun (hz _ h0) i)
  change (1 : Af F) * (z i).2 = 0 at h
  rwa [one_mul] at h

theorem finPart_add (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  unfold finPart
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  have h : evFin F v (z i) = 0 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
    rw [snd_eq_zero_of_at z hz i, map_zero]
  rw [Pi.add_apply, map_add, h, add_zero]

end GlobalTheory.EvZeroInf
