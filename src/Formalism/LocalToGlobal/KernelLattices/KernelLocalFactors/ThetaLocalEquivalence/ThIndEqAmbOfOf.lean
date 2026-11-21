import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.CharacterFactorUnitaryAction
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VacEntire
import Formalism.PeriodIntegrals.VacEntire
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.GMConjTranspose

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section U

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem TE.ufGL_apply' (γ : UF E n) (i j : Fin n) : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = γ.1 (Pi.single j 1) i := by
  have h := TE.matT_apply (ι := Unit) (fun _ => RingHom.id E) γ () i j
  simpa [TE.matT] using h

theorem TE.ufInv_apply (γ : UF E n) (i k : Fin n) : γ.1.symm (Pi.single k 1) i = star (γ.1 (Pi.single i 1) k) := by
  have h : hStd E n (γ.1 (Pi.single i 1)) (γ.1 (γ.1.symm (Pi.single k 1))) = hStd E n (Pi.single i 1) (γ.1.symm (Pi.single k 1)) :=
    γ.2 _ _
  rw [LinearEquiv.apply_symm_apply, hStd_single_left] at h
  rw [← h, hStd_apply]
  simp [Pi.single_apply]

end U

end Formalism.L2.Ker
