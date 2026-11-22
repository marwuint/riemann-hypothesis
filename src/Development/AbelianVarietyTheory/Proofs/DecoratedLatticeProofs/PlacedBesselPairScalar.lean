import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupScalarAtFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlaceFrameExists

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop.UnitAtLevel

theorem smulOne_mulVec {R : Type} [CommRing R] {n : ℕ} (c : R) (y : Fin n → R) :
    Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y = c • y := by
  funext i
  rw [Matrix.smul_one_eq_diagonal, Matrix.mulVec_diagonal]
  rfl

theorem inv_of_scalar {R : Type} [CommRing R] {n : ℕ} (hn : 0 < n) (A : GL (Fin n) R) (c : R)
    (hA : A.val = c • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ ι : R, ι * c = 1 ∧ (A⁻¹).val = ι • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : (A⁻¹).val * A.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  rw [hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] at h2
  refine ⟨(A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩, by rw [mul_comm]; exact h2, ?_⟩
  have h3 : A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    rw [hA, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, one_smul]
  calc (A⁻¹).val = (A⁻¹).val * (A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R))) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mem_of_shift {R : Type} [CommRing R] (O : Subring R) (a u ι : R) (ha : ∃ a', a' * a = 1) (hι : ι * u = 1)
    (key : ∀ c, a * c ∈ O ↔ a * (ι * c) ∈ O) : u ∈ O ∧ ι ∈ O := by
  obtain ⟨a', ha'⟩ := ha
  have e1 : a * a' = 1 := by rw [mul_comm]; exact ha'
  have e2 : a * (ι * a') = ι := by linear_combination ι * e1
  have e3 : a * (ι * (a' * u)) = 1 := by linear_combination (ι * u) * e1 + hι
  have e4 : a * (a' * u) = u := by linear_combination u * e1
  constructor
  · have := (key (a' * u)).2 (by rw [e3]; exact O.one_mem)
    rwa [e4] at this
  · have := (key a').1 (by rw [e1]; exact O.one_mem)
    rwa [e2] at this

end GlobalTheory.MiTop.UnitAtLevel

namespace GlobalTheory.MiTop

end GlobalTheory.MiTop

end
