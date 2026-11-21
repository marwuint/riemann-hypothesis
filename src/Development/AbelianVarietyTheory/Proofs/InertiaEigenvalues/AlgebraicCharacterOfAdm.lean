import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisAdmissibleIffRepPureAvatar

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.AlgCharFromGal

theorem charpoly_fin_one {K : Type*} [CommRing K] (M : Matrix (Fin 1) (Fin 1) K) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

end GlobalTheory.AlgCharFromGal

end
