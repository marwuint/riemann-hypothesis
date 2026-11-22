import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowLocalAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlaceCuspidalType
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutantFullOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem exists_heq_of_eq {F : D7 → Sort _} {D₁ D₂ : D7} (h : D₁ = D₂) (x : F D₁) : ∃ y : F D₂, HEq y x := by
  subst h; exact ⟨x, HEq.rfl⟩

end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem heq_cf_of_pack {p q : Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁} (h : p = q) :
    HEq p.2.1 q.2.1 := by
  subst h; rfl

end GlobalTheory.RowTriple.Lay
