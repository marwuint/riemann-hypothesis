import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLa
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdForm_apply (K : Type) [Field K] [StarRing K] (M : ℕ) (x y : Fin M → K) :
    StandardLattice.stdForm K M x y = ∑ i, star (x i) * y i := rfl

theorem std_ortho (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) :
    IsOrthoLattice (StandardLattice.stdForm K M) (StandardLattice.stdLat K M) M := by
  have e : (fun i : Fin M => (Pi.single i 1 : Fin M → K)) = Pi.basisFun K (Fin M) := by
    funext i; simp
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, fun i j => ?_⟩
  · rw [e]; exact (Pi.basisFun K (Fin M)).linearIndependent
  · rw [e]; exact (Pi.basisFun K (Fin M)).span_eq
  · by_cases hij : i = j
    · subst hij; simp [stdForm_apply, Pi.single_apply]
    · simp [stdForm_apply, Pi.single_apply, hij, Ne.symm hij]

end Formalism.MainNotions.J

end
