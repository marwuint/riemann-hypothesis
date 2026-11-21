import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointsNonemptyUnitaryGaussian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.ComplexUniformization

variable {p : ℕ} [Fact p.Prime]

structure MP (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) where

  Dl : PLat D.O D.inv

  t : D.La → Dl.La

  P : Dl.La →+ (Fin D.g → ℂ)
  cls : D.Cls N Dl t
  per : IsPeriod Dl ρ P

def TypeAt (D : Datum p) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (D.m : ℂ) * (∑ i, D.tau i (c : D.F) +
    ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
    ∑ i, (starRingEnd ℂ) (D.tau i (c : D.F)))

variable {D : Datum p} {G : HTGroup p}

end UpperTheory.ComplexUniformization
