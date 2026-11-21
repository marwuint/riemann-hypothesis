import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.RealDimOne

open GlobalTheory.TorsionGenerators NumberField

theorem isPrimitiveRoot_unitOn {k : Type} [CommRing k] {u : kˣ} {M : ℕ} (h : IsPrimitiveRoot u M) :
    IsPrimitiveRoot (unitOn u) M :=
  h.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) unitOn_injective

theorem unitOn_zpow {k : Type} [CommRing k] (u : kˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) u n

end GlobalTheory.ZH.RealDimOne
