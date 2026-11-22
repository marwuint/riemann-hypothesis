import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MuLift

section Adelic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E)) (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ IsConjPl Q Q') :
    ∃ e : AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')

end Adelic

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.MuLift

end
