import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointAction

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwCx

open GlobalTheory.ExportSeries Formalism.IndefR.Datum GlobalTheory.BigOn.Exp.TupLe GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)

def TwQ : Prop := ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (Q : Finset (Pl D.host.E))
  (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), IntegralHeckeForms.TwOK i k Q ψ → ∀ P ∈ Q, ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

theorem twQ : TwQ := by
  intro D i k Q ψ hok P hP hl
  obtain ⟨-, -, -, -, -, hram, htriv⟩ := hok
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P
  obtain ⟨σ, hσ, hne⟩ := (hram P A hA).2 hP
  exact hne (htriv P hl A hA σ (ReciprocityTheory.Gal.Ine_le_Dec A hσ))

end GlobalTheory.BigOn.Exp.TwCx
