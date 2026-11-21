import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVa
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)

end Formalism.MainNotions.J

end
