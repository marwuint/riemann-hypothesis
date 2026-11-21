import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.ZeroComplOfFb
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.CoeSmEqSymm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightInfGLLeOpNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightGeArchOpNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelSetInterTranslateFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelH
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.MemIffLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.CentralScalar

noncomputable section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Af Matrix

namespace Ad3P.CuspidalityAtInfinity

section Bridge

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

variable {V : Submodule ℂ (Ad3.G3 → ℂ)} (hV : Ad3.WhA V)

def incl : V →ₗ[ℂ] archSmooth ℚ 3 where
  toFun W := ⟨W.1, hV.arch W.1 W.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def DV (i j : Fin 3) : Module.End ℂ V :=
  LinearMap.codRestrict V ((archSmooth ℚ 3).subtype ∘ₗ Ad3.EA i j ∘ₗ incl hV) fun W => hV.lie _ W.2 i j

theorem incl_DV (i j : Fin 3) (W : V) : incl hV (DV hV i j W) = Ad3.EA i j (incl hV W) := rfl

end Bridge

section Local

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic

open scoped ValuativeRel

private theorem psi_eq (w : Ad3.Pl) (x : Ad3.Qv w) :
    (Circle.coeHom.compAddChar (localAdelicChar ℚ w)) x = UpperTheory.V.Af.Smo.psiL w x := rfl

end Local

end Ad3P.CuspidalityAtInfinity
