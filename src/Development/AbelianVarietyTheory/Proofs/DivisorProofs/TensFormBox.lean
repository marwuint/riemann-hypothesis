import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def repl (v : Pl F) (y : κ → AF F) (x : κ → Fv F v) : κ → AF F :=
  fun i => y i - liftV v (evFin F v (y i)) + liftV v (x i)

def proj (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ y := φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x)
  map_add' Φ Ψ := by
    funext y
    rw [Pi.add_apply, ← mul_add, ← map_add]; rfl
  map_smul' c Φ := by
    funext y
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← smul_eq_mul c, ← map_smul]; rfl

theorem proj_apply (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (Φ : (κ → AF F) → ℂ)
    (y : κ → AF F) : proj v φ₀ l Φ y = φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x) := rfl

end GlobalTheory.MixedForm

end
