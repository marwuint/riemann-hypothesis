import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionAtGoodPoints
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension

noncomputable section

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem UpperTheory.GalS.jointCondition_of_constituentCondition_split (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (h : UpperTheory.GalS.DistinctAbsIrredConstituents D.nd i r) (hS : GlobalTheory.SplitCoef.OSplitAt D i) : AbsIrreducibleDistinct D i r := by
  obtain ⟨K', hK', hA, _, hK⟩ := h
  exact _root_.GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct D i r hS hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)
end

namespace GlobalTheory.CrysFromGTwo

end GlobalTheory.CrysFromGTwo
namespace GlobalTheory.DualTwistCrys

end GlobalTheory.DualTwistCrys
namespace GlobalTheory.CrysChiOne
end GlobalTheory.CrysChiOne
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
