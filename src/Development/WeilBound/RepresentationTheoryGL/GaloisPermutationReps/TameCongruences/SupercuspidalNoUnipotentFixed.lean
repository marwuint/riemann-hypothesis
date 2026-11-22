import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.CongruenceClosedIdempotent
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.UnitaryBC GlobalTheory.CuspRep
open PositivityTheory.Rg.DzCount (FinCusp IsTypeMap Fwd)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCong

structure In : Prop where
  llc : GlobalTheory.Published.LocalLanglandsExists
  conv : GlobalTheory.Published.LocalConverseGL
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  multi : GlobalTheory.Published.LanglandsMultisegments
  cos : GlobalTheory.Published.StandardCosocleGL
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  geo : GlobalTheory.Published.GeometricLemma
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  bcs : GlobalTheory.BcSpeh.BcSpeh
  gal : GlobalTheory.Published.PolarizedGaloisRepPublished
  gk : GlobalTheory.Published.GelfandKazhdanDual

end PositivityTheory.Rg.DzCong

end
