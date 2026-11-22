import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.KFinStable

end GlobalTheory.KFinStable

noncomputable section

namespace GlobalTheory.KFinStable

variable {n : ℕ}

def kSub (ε : Fin n → Bool) : Subgroup (Matrix.unitaryGroup (Fin n) ℂ) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * g}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    show (a : Matrix (Fin n) (Fin n) ℂ) * b * Jm ε = Jm ε * (a * b)
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by
    show ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * _
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    show star (a : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * star (a : Matrix (Fin n) (Fin n) ℂ)
    have h := congrArg star ha
    simp only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] at h
    simpa [Matrix.star_eq_conjTranspose] using h.symm

instance unitaryGroup_compactSpace' (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)

instance matrix_secondCountable' (m : ℕ) : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))

instance unitaryGroup_secondCountable' (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance kSub_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (kSub ε) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance kSub_compactSpace (ε : Fin n → Bool) : CompactSpace (kSub ε) := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  have : IsClosed {g : Matrix.unitaryGroup (Fin n) ℂ |
      (g : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * g} :=
    isClosed_eq ((continuous_subtype_val).mul continuous_const)
      (continuous_const.mul continuous_subtype_val)
  exact this

end GlobalTheory.KFinStable

noncomputable section

namespace GlobalTheory.KFinStable

end GlobalTheory.KFinStable
