import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section
namespace GlobalTheory.NLink.AmbSub

variable {D : D7}

theorem WpO_cont (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous fun g => WpO D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul hρ

end GlobalTheory.NLink.AmbSub
