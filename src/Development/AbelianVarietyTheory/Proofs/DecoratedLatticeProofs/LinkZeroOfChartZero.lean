import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem besLev_per_congr {D : D7} {ρ : ℕ} {B B' : BesLev D ρ} (h : B = B') (ψ) {φ : GA D B.A → ℂ} {φ' : GA D B'.A → ℂ}
    {g : GA D B.V → ℂ} {g' : GA D B'.V → ℂ} (h1 : HEq φ φ') (h2 : HEq g g') : B.per ψ φ g = B'.per ψ φ' g' := by
  subst h
  rw [eq_of_heq h1, eq_of_heq h2]

end GlobalTheory.MiTop
