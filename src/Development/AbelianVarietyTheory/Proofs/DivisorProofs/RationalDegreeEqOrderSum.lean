import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.RatDegZeros

theorem mem_range_fst : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → x ∈ Set.range (ratFibre.fst p) := by
  intro k _ X p x hx
  let q : Spec (X.residueField x) ⟶ Sp ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (X.residueField x)))
  let y0 := (ratFibre.isPullback p).lift (X.fromSpecResidueField x) q (specZIsTerminal.hom_ext _ _)
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  refine ⟨y0 z, ?_⟩
  have e : (y0 ≫ ratFibre.fst p) z = X.fromSpecResidueField x z := by
    rw [(ratFibre.isPullback p).lift_fst]
  rw [Scheme.Hom.comp_apply] at e
  exact e.trans (X.fromSpecResidueField_apply x z)

end GlobalTheory.RatDegZeros
