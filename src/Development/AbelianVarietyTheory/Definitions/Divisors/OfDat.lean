import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {Tw : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}

theorem TiesG.of_dat (z : Dat X I hX Tw Wt) (hU : z.R.toRealDat.LUnif) (hI : IoExt z.R.toRealDat)
    (hM : ∀ i, OneMapRowR z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) i)
    (hC : GlobalTheory.TwistField.CoverField z.core z.R.toRealDat) : TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have e : (fun i => cj (twAt X.toD7.what₂.embLL (famR X I hX (usedOf I Tw Wt) z.Xg z.tr).A.v0) (z.R.phs i)) = fun _ => (1 : ℂ) := by
    funext i
    rw [z.pins.phs i]
    exact map_one _
  refine ⟨⟨z.geo.fw, z.geo.bar⟩, z.geo.pins, ?_, hU, hI, ?_, hC⟩
  · rw [e]; exact z.geo.phase
  · rw [e]; exact hM

end GlobalTheory.PrimIn

end
