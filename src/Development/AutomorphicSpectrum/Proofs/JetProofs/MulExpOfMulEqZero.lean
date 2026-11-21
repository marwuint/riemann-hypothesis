import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocSizeBlocks
import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.HCSide

section Circle

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def circleSpace (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) : Submodule ℂ H where
  carrier := {x | ∀ z : ℂ, ‖z‖ = 1 → π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x}
  zero_mem' := fun z _ => by simp
  add_mem' := fun {x y} hx hy z hz => by rw [map_add, hx z hz, hy z hz, smul_add]
  smul_mem' := fun c x hx z hz => by rw [map_smul, hx z hz, smul_comm]

theorem mem_circleSpace {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {m : ℤ} {x : H} :
    x ∈ circleSpace π m ↔ ∀ z : ℂ, ‖z‖ = 1 → π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x := Iff.rfl

theorem isClosed_circleSpace (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) :
    IsClosed (circleSpace π m : Set H) := by
  have : (circleSpace π m : Set H) =
      ⋂ z : ℂ, ⋂ _ : ‖z‖ = 1, {x | π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x} := by
    ext x; simp [mem_circleSpace]
  rw [this]
  exact isClosed_iInter fun z => isClosed_iInter fun _ =>
    isClosed_eq (π _).continuous (continuous_const_smul _)

instance [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) :
    CompleteSpace (circleSpace π m) :=
  (isClosed_circleSpace π m).completeSpace_coe

end Circle

end GlobalTheory.CompanionTheory.HCSide

end
