import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockTypeVectorIrreducibleSplitsAsProduct

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypesAtPin

theorem not_over_g_of_mem_Q (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ D.nd.Q i)
    (k : Fin 2) : w ∉ placesOver D.host.E (D.host.g k) := by
  intro hk
  have hS : w ∈ D.nd.S i := (D.nd.S_def i w).2 ⟨by
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk), D.nd.SQ_l i w (Or.inr hw)⟩
  exact Finset.disjoint_left.1 (D.nd.SQ_disj i) hS hw

end GlobalTheory.TypesAtPin
