import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous

noncomputable section

namespace GlobalTheory.ChrWSmooth

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_chrW {χ : Chr F E} (hχ : Continuous χ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    Continuous (chrW χ t) := by
  have hm : Continuous (Units.map (complMap (splitPrime_under t)).toMonoidHom) :=
    Units.continuous_map (GlobalTheory.LFun.SplitChart.continuous_complMap (splitPrime_under t))
  have h1 : Continuous fun x : (Fv F v)ˣ => ((chrW χ t x : ℂˣ) : ℂ) :=
    (continuous_locChar hχ (splitPrime t)).comp hm
  have h2 : Continuous fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((chrW χ t x⁻¹ : ℂˣ) : ℂ) := by
      funext x; rw [map_inv]
    rw [this]
    exact h1.comp continuous_inv
  exact Units.continuous_iff.2 ⟨h1, h2⟩

theorem isUnitaryChar_chrW (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SmGL.IsUnitaryChar (chrW χ t) := fun g => by
  show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _

end GlobalTheory.ChrWSmooth
