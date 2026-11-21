import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

open private hasSupport_contra from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
open private goodCusp_dualCl from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_contra {n : ℕ} (π π' : IrrRep (GL (Fin n) k)) (e : Nonempty (π'.ρ.Equiv (contra π.ρ))) (hg : Good (cls π)) :
    Good (cls π') := by
  obtain ⟨s, h1, h2⟩ := hg
  obtain ⟨φ⟩ := e
  have h3 : HasSupport π.ρ s := h1.of_equiv (equivRep π).symm
  refine ⟨s.map Zc.dualCl, ((hasSupport_contra h3).of_equiv φ.symm).of_equiv (equivRep π'), fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
  exact goodCusp_dualCl (h2 z hz)

end

end UpperTheory.One.M
