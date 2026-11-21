import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.Reindex

attribute [local instance] Over.cartesianMonoidalCategory

variable {g g' : ℕ}

noncomputable def rho (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε i)

theorem rho_apply (ε : Fin g' ≃ Fin g) (z : Fin g → ℂ) : rho ε z = z ∘ ε := rfl

noncomputable def rhoM (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) ≃ᵐ (Fin g' → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) ε).symm

theorem rhoM_eq (ε : Fin g' ≃ Fin g) : ⇑(rhoM ε) = ⇑(rho ε) := rfl

end GlobalTheory.FrameEquiv.Reindex

namespace GlobalTheory.FrameEquiv

end GlobalTheory.FrameEquiv
