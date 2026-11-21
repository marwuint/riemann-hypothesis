import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)

namespace LateralTheory.EWeil.ArtinCut

instance (X : Scheme.{0}) : HasSheafify X.smallEtaleTopology AddCommGrpCat.{1} := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  infer_instance

instance (X : Scheme.{0}) : IsGrothendieckAbelian.{1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

instance (X : Scheme.{0}) : HasExt.{1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) := inferInstance

abbrev Sm (A : CommRingCat.{0}) : Type 2 := Sheaf (Spec A).smallEtaleTopology AddCommGrpCat.{1}

end LateralTheory.EWeil.ArtinCut

end
