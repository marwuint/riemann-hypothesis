import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr

namespace UpperTheory.GalN.V

theorem dual_two {Γ k : Type} [Group Γ] [Field k] (W : Γ →* GL (Fin 2) k) : DualTw W (Matrix.GeneralLinearGroup.det.comp W) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => by
    have hd : ((Matrix.GeneralLinearGroup.det.comp W s : kˣ) : k) = (W s).val.det := rfl
    rw [hd, Matrix.det_fin_two (W s).val]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring⟩

end UpperTheory.GalN.V
