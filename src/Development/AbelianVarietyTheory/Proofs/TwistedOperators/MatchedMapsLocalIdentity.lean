import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThK.PolMatchStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_lin_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ)) {φ ψ φ₁ ψ₁ χ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (hψ : ψ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T ψ ψ₁) (a b : ℂ) (h₃ : Acts (evFin F v) T (a • φ + b • ψ) χ) :
    χ = a • φ₁ + b • ψ₁ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hs : a • φ + b • ψ ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem a hφ) ((SB _).smul_mem b hψ)
  have hlin : ∀ x y : (κ → Fv F v) → ℂ,
      tens (evFin F v) (a • x + b • y) R = a • tens (evFin F v) x R + b • tens (evFin F v) y R := by
    intro x y; funext z; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  refine GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ hs).1 ?_
  rw [← h₃ R (hR _ hs), hlin, map_add, map_smul, map_smul, h₁ R (hR _ hφ), h₂ R (hR _ hψ), hlin]

open Classical in

theorem pure_update (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f : SInf F κ)
    (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (κ → Fv F w))
    (hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ₁ : (κ → Fv F v) → ℂ} (hA : Acts (evFin F v) T (φ v) φ₁) :
    T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = tens (evFin F v) (φ v) r := by rw [hrt, Function.update_eq_self]
  have hRest : Rest (evFin F v) (φ v) r := ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  rw [e1, hA r hRest, hrt]

end Local

end GlobalTheory.ThK.PolMatchStep

end
