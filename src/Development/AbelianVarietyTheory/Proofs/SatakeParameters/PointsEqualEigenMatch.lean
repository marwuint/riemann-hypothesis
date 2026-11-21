import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompletionEquivUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BiInvariantHeckeOpScalarOnSphericalIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarOnIsotypicPart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypic

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigAgree

end GlobalTheory.EigAgree

theorem GlobalTheory.EigAgree.cast_ne_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a) (hf : f ≠ 0) :
    (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  subst h
  exact hf

