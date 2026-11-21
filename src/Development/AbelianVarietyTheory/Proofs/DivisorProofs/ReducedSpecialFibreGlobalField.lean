import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.RedFibreField

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite in
open Scheme.IdealSheafData in

theorem _root_.GlobalTheory.RedFibreField.isReduced_nilradical_subscheme (X : Scheme.{0}) : IsReduced X.nilradical.subscheme := by
  have h : X.nilradical = vanishingIdeal (⊥ : X.IdealSheafData).support := by
    rw [Scheme.nilradical, vanishingIdeal_support]
  rw [h]
  exact _root_.GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _

end

end GlobalTheory.RedFibreField

namespace GlobalTheory.RedFibreField

end GlobalTheory.RedFibreField
