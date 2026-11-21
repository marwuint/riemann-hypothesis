import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoeffRowAct

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace GlobalTheory.CompanionTheory.CxAvg

section Concrete

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC

variable {n : ℕ}

local notation "KU" n => Matrix.unitaryGroup (Fin n) ℂ

instance secondCountable_unitary : SecondCountableTopology (KU n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _

theorem Rm_unitary (lam : Fin n → ℤ) (k : KU n) :
    Rm lam k.1 = LinearMap.toMatrix (wb lam) (wb lam)
      (GlobalTheory.Branching.sqRep ℂ n (dw lam) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dif_pos h, e]

theorem Rm_mul (lam : Fin n → ℤ) (k k' : KU n) : Rm lam (k * k').1 = Rm lam k.1 * Rm lam k'.1 := by
  rw [Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : KU n).1 = 1 := by
  rw [Rm_unitary, map_one, map_one]
  exact LinearMap.toMatrix_id _

theorem continuous_unitaryIncl : Continuous (GlobalTheory.Branching.unitaryIncl n) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem continuous_Rm (lam : Fin n → ℤ) : Continuous fun k : KU n => Rm lam k.1 := by
  simp only [Rm_unitary]
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp
    continuous_unitaryIncl

theorem conj_val (k : KU n) : k.1ᴴ = (k⁻¹).1 := rfl

end Concrete

end GlobalTheory.CompanionTheory.CxAvg
