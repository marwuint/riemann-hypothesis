import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockAlg

theorem fock_structure : ∀ X : ProvA, admH2 X := by
  intro X p q r s
  refine ⟨fun d μ P hP hw => (_root_.GlobalTheory.FockAlg.degW_le_of_homog_wtSub p q r s).1 d μ P hP hw.1 hw.2.1,
    fun d μ P hP hw => (_root_.GlobalTheory.FockAlg.degW_le_of_homog_wtSub p q r s).2 d μ P hP hw.1 hw.2.1,
    fun μ P h0 ht hh => (_root_.GlobalTheory.FockAlg.harmonic_homog_of_type p q r s).1 μ P h0 ht hh,
    fun μ P h0 ht hh => (_root_.GlobalTheory.FockAlg.harmonic_homog_of_type p q r s).2 μ P h0 ht hh,
    fun μ μ' => ⟨_root_.GlobalTheory.JointHarm.finrank_joint_highest_of_shape p q r s μ μ', _root_.GlobalTheory.FockAlg.jointHarm_hw_eq_bot p q r s μ μ'⟩, ?_⟩
  intro u1 u2 hu d
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.FischerParts.fischer_parts p q r s d
  cases u1 <;> cases u2
  · simp at hu
  · have e1 : lowKer X (X.fock p q r s) false true = harm1 p q r s := by
      ext P; simp [lowKer, harm1, FockData.act2]
    have e2 : raised X (X.fock p q r s) false true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act2]
    rw [e1, e2]; exact h2
  · have e1 : lowKer X (X.fock p q r s) true false = harm2 p q r s := by
      ext P; simp [lowKer, harm2, FockData.act1]
    have e2 : raised X (X.fock p q r s) true false d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1]
    rw [e1, e2]; exact h1
  · have e1 : lowKer X (X.fock p q r s) true true = jointHarm p q r s := by
      ext P; simp [lowKer, jointHarm, harm1, harm2, FockData.act1, FockData.act2]
    have e2 : raised X (X.fock p q r s) true true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨
          ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1, FockData.act2]
    rw [e1, e2]; exact h3

end GlobalTheory.FockAlg
