import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfDeltaFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReading
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExport
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericType
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndex
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlaceCuspidalType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutantFullOfLocalLanglands

noncomputable section

namespace GlobalTheory.TwInputs.AtLayer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section General

variable {D : D7}

theorem injective_of_cellTie {ρ : Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) : Function.Injective rd := by
  refine (injective_iff_map_eq_zero rd).2 fun x hx => ?_
  have h1 : ((1 : D.ntw.Ok i 0) ⊗ₜ[D.ntw.O i] x : D.ntw.Ok i 0 ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) = 0 :=
    T.injective_rdK 0 (by rw [rdK_tmul, hx, smul_zero, map_zero])
  haveI : Module.Flat (D.ntw.O i) (FractionRing (D.ntw.O i)) := IsLocalization.flat _ (nonZeroDivisors (D.ntw.O i))
  haveI : Module.Flat (D.ntw.O i) (D.nexp.Fm i ((j : ℕ) + 1) b) :=
    Module.Flat.trans (D.ntw.O i) (FractionRing (D.ntw.O i)) _
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := D.nexp.Fm i ((j : ℕ) + 1) b)
    (Algebra.linearMap (D.ntw.O i) (D.ntw.Ok i 0)) (D.ntw.Ok_inj i 0)
  have h3 : ((1 : D.ntw.O i) ⊗ₜ[D.ntw.O i] x : D.ntw.O i ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) = 0 := h2 (by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one, h1, map_zero])
  simpa using congrArg (TensorProduct.lid (D.ntw.O i) _) h3

def IsFrobUnit (D : D7) (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) : Prop :=
  ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    u i b P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹)

theorem exists_hecke (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j))
    (h0 : ∀ j P, hL j 0 P = 1) (hr : GlobalTheory.ExportPin.Reads X.R X.cG S YS hL)
    (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) (hu : IsFrobUnit D u)
    (hz : ∀ i j b P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j b 0 P x = x) :
    ∃ H : NExpRealH X.R X.cG S YS, GlobalTheory.ExportPin.Reads X.R X.cG S YS H.hL ∧
      ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (algebraMap (D.ntw.O0 i) (D.ntw.O i)
          ((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  have hδ : IsDeltaInv Z.ρ u := by
    intro i j b k P hk α z hα hz
    have e : u i b P = HeckePinRead.uD D i b P := by
      rw [hu i b P hk.2.2.2 _ (HeckePinRead.frobU_spec D P)]
      cases b <;> rfl
    rw [e]
    exact HeckePinRead.isDeltaInv_uD Z.good Z.pin i j b k P hk α z hα hz
  refine ⟨⟨hL, hs, fun i b k P => (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k,
    fun _ _ _ => pow_zero _, fun i b P => ((u i b P).isUnit.map _).pow 1, fun i b k P => by rw [pow_one], ?_⟩, hr, ?_⟩
  · intro i j b h1 h2 k P x hP hsp hk
    rcases Nat.eq_zero_or_pos k with rfl | k1
    · rw [hz i j b P x h1 h2 hP hsp, pow_zero, one_smul,
        (GlobalTheory.ExportPin.Model.hkFR_of_smul S i j b (hs j h1 h2) 0 P).2 (h0 j P)]
      rfl
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      let j' : Fin D.R.m := ⟨n, h2⟩
      have hk' : HkIdx i k P := ⟨k1, hk, hsp, hP⟩
      obtain ⟨α, R, z, d⟩ := GlobalTheory.HeckeDatumExists.exists_isHeckeDatum D _ _ Z.ρ Z.good i j' b k P hk'
      have e := (Z.hecke i j' b).eq (injective_of_cellTie (Z.tie i j' b)) hk' d
        (heckeAt_of_scaled YS X.geo.v₀ Z.pin X.char.lev X.char.allPl Z.good hr hδ i j' b (Z.ν i j' b)
          (hs _ (Nat.le_add_left _ _) j'.2) hk' (f := x) ((YS.eF i _ b (Nat.le_add_left _ _) j'.2).apply_symm_apply _))
      exact (congrArg (YS.eF i _ b h1 h2) e).trans ((YS.eF i _ b h1 h2).apply_symm_apply _)
  · intro i b P hP σ hσ
    change (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ 1 = _
    rw [pow_one, hu i b P hP σ hσ, Units.coe_map]
    rfl

theorem hkF_zero_of_sideB {cf Rw low Pq S hL eig θ} (Bs : SideB D cf Rw low Pq S hL eig θ) (h0 : ∀ j P, hL j 0 P = 1) :
    ∀ i j b P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j b 0 P x = x := by
  intro i j b P x h1 h2 hP hsp
  refine (Bs.eF i j b h1 h2).injective ?_
  rw [Bs.hkEq i j b h1 h2 0 P x hP hsp (Nat.zero_le _), pow_zero, one_smul]
  exact LinearMap.congr_fun ((GlobalTheory.ExportPin.Model.hkFR_of_smul S i j b (Bs.hs j h1 h2) 0 P).2 (h0 j P)) _

end General

end GlobalTheory.TwInputs.AtLayer

namespace GlobalTheory.TwInputs.AtLayer

end GlobalTheory.TwInputs.AtLayer

end
