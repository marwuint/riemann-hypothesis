import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAutomorphicVectorSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompact

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.StrSplitDict.cast_ne_zero : ∀ (D : D7) (μ : D.what₂.Tup) (a b : ℕ) (h : a = b) (f : D.what₂.Mt μ a), f ≠ 0 → (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  intro D μ a b h f hf
  subst h
  exact hf

