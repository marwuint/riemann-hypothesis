import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldAbelianTameIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormula
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lie

variable {k : Type} [Field k] [NumberField k] {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)}

theorem isEigBasis_iff (τ : E →+* k) : EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) x ↔
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x := Iff.rfl

end Lie

section Extension

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}

structure IsUnder (i : k →+* k') (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k))
    (ε : HeightOneSpectrum (𝓞 k') → ℕ) : Prop where
  val : ∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓
  sum : ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧
    (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) =
      (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal)

variable {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}

variable {t : SAB H (Sp k)} {t' : SAB H (Sp k')}

end Extension

end GlobalTheory.FlatDegreeCompare
