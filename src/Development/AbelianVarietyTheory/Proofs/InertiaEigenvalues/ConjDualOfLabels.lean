import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTranspose
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWildStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneLabelTransportDualInverseRootsStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjPlaceDual

theorem conjPl_symm (D : D7) {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hy, GlobalTheory.SplitPlaceOver.host_conj_eq', GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

end GlobalTheory.ConjPlaceDual
