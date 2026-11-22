import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.LiftExponentAdmissibleColsRowsOfCrystalline
import Development.AutomorphicArithmetic.ResidueCharacters.BlockConditionAtPlacesOfJumpWindow
import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsLengthAdmissibleOfNonzeroJumps
import Development.AutomorphicArithmetic.ResidueCharacters.AmbOfSetPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG5Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolySpanAndHomRelationsOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

open Classical in

def withDc {D : D7} (X : KillingConditions.HubData D) (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) : KillingConditions.HubData D :=
  { X with dc := Function.update X.dc i dc }

open Classical in
theorem withDc_dc {D : D7} (X : KillingConditions.HubData D) (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) : (withDc X i dc).dc i = dc := by
  simp only [withDc, Function.update_self]

end UpperTheory.N

end
