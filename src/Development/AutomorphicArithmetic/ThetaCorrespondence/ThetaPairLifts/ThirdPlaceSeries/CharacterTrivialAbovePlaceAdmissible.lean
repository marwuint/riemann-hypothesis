import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsobaricRigidOfPin
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem character_trivial_above_place_admissible_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    Formalism.MainNotions.SumRepresentations.adm5 D := by
  have hrig : IsobaricRigid D.nd D.naut := _root_.GlobalTheory.NPin.isobaricRigid_of_pin_alt hPr.fin hPr.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.cheb D
  exact (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
end GlobalTheory.ChiOneAbove
end
end
