import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRule
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDictModel

open GlobalTheory.HolDict

section Adelic

variable {D : D7}

theorem fix_iff (τ : D.host.E →+* ℂ) :
    τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD ↔ ∃ ρ, τ = tauE D ρ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  have h1 : D.host.galE (D.host.sigmaOf g) = g :=
    (D.host.gal).apply_symm_apply g
  refine Iff.trans ?_ (Formalism.L2.Geo.exists_tauEmb_iff D g).symm
  conv_rhs => rw [← h1]
  refine Iff.trans ?_ (D.host.galE_mem_Psi_iff _).symm
  exact ⟨fun h => D.host.φ₀.injective h, fun h => congrArg D.host.φ₀ h⟩

end Adelic

end GlobalTheory.HolDictModel
