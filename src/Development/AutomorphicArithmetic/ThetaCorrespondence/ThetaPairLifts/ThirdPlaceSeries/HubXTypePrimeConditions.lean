import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeExceedsConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace UpperTheory.GalS
theorem noLgc_alt : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → NoCondition D := fun _ _ _ _ _ => trivial
theorem hubX_typePrime_conditions_alt : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → AdmissibleParameterJ.JumpConditions L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → SumRepresentations.ConclusionG5 D → _root_.UpperTheory.GalS.NoCondition D → GlobalTheory.HubX.DepthZeroG D → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  intro D L HW R X hX P hJ hadm hG5 hLgc hDZ CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hadm' : L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := hadm
  have hb : 1 ≤ L.sc.b := by linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.b := by linarith
  obtain ⟨hnum1, hnum2, hnum3⟩ := GlobalTheory.typePrime_exceeds_constant D L P (by linarith) hb CT hCT
  obtain ⟨hJa, hJb, hJc, -, hJe, -, -⟩ := hJ
  have hJaAt : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D (GlobalTheory.HubX.epJ D) := by
    rw [GlobalTheory.HubX.epJ_eq hJa]; exact hJa.choose_spec
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hX.fam.good
  have hpt := _root_.GlobalTheory.PointConditions.main D X.r X.ρ hX.fam
  rw [hX.eta]
  refine ⟨fun i k _ hk hHG => ⟨hgood i, fun π hπ => ⟨(hpt i π hπ).1, (hpt i π hπ).2.1⟩, ?_⟩, hnum2⟩
  obtain ⟨sg, U, hsg, hU⟩ := _root_.GlobalTheory.HostJumpSets.main D L (GlobalTheory.HubX.epJ D) hJaAt hJb hJc hJe ht i k (X.r i) hk (hgood i)
  refine ⟨⌊3 * L.sc.b⌋₊ + 2, 0, sg, U, hnum1, hnum3 k, hsg, hU⟩
end UpperTheory.GalS
end
