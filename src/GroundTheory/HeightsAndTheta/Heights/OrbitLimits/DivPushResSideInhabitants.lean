import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

abbrev ProjRegular.pointV : Set ProjectiveLineResolution.res.X := {((0 : ℂ) : OnePoint ℂ)}

instance ProjRegular.instUniquePointV : Unique ProjRegular.pointV :=
  Set.uniqueSingleton _

end GroundTheory.Heights₂.Heights.Targets
