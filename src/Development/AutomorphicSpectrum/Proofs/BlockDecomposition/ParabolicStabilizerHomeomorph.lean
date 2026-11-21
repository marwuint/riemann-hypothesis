import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QMatInjective
noncomputable section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GroundTheory.Automorphic
open scoped InnerProductSpace Topology ENNReal NNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.ModP.StabEquiv

variable {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a}

theorem uMat_mul' (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one' : uMat (1 : UJ ε) = 1 := rfl

instance topAddGroup_qAlg (ε : Fin n → Bool) (W : Flag n a) : IsTopologicalAddGroup (qAlg ε W) :=
  inferInstanceAs (IsTopologicalAddGroup (Subalgebra.toSubmodule (qAlg ε W)))

instance continuousSMul_qAlg (ε : Fin n → Bool) (W : Flag n a) : ContinuousSMul ℝ (qAlg ε W) :=
  ⟨Continuous.subtype_mk
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩

end GlobalTheory.CompanionTheory.ModP.StabEquiv

namespace GlobalTheory.CompanionTheory.ModP

end GlobalTheory.CompanionTheory.ModP
