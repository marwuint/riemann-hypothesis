import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonneg
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAtPlaceOfIntegralCoverReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCover
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.DescLoc

theorem holSub0_of_cusp : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ T.cuspA j a n, rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) a n) := by
  intro D T j a n f hf
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ a n ⟨f, hf⟩

theorem desc_loc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVstd hV hFP l hl C hC hPin la hla hUn φ hφ hKf m x ψ hψ hsum
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hU := hC.1
  choose f hf hfψ using hψ
  have hfc : ∀ b, f b ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := fun b =>
    _root_.GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 D T hL _ hj (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs hTie.kap i) (f b) (hf b).1 (hf b).2
  obtain ⟨p, hbelow, hlp, hval⟩ := _root_.GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below _ _ C.inc l hl la hla hUn
  obtain ⟨la', hla'⟩ := _root_.GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv _ _ C.d.eF.toRingEquiv la
  let x' : Fin m → C.c'.F := fun b => C.d.eF.symm (x b)
  have hx' : ∀ b, C.d.eF (x' b) = x b := fun b => C.d.eF.apply_symm_apply (x b)
  have hφ' : (∑ b, C.σ₂ (C.d.eF (x' b)) • T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (f b)) ∈
      C.intForms (wtA (κ i)) (κ i).n {la} := by
    simp only [hx', hfψ]
    rw [← hsum]
    exact hφ
  have hint := _root_.GlobalTheory.CoverLocInt.bddAll_of_mem_intForms D T hL _ hj T.σ₀ T.good_σ₀ C hU (wtA (κ i)) (κ i).n (dom_wtA (κ i)) hPin la la'
    (fun y => hla' y) m x' f (fun b => (hf b).1) hφ'
  have hmem : (∑ b, x' b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈
      cusp (T.Q.Xo ((i : ℕ) + 1)) C.c' (unfBC C.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
      ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ C.hle _ (T.U ((i : ℕ) + 1)) _ _ (f b) (hf b).1).2.2 (hfc b))
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hvLa : ∀ y : T.Q.c.F, vLa la' (incF T.Q.c C.c' C.hle y) = vLa p y := fun y => by
    unfold vLa
    rw [hla', ← hval]
    rfl
  obtain ⟨m', as, fs, has, hfs, hBC⟩ := _root_.GlobalTheory.SupDescent.supSet_descent _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hL.unf _ hj) p l hl hlp hgood
    C.c' C.hle la' hvLa (GlobalTheory.SecFieldChange.cuspBC_holds C.hle _) (wtA (κ i)) (κ i).n (dom_wtA (κ i))
    (hL.cuspFD _ hj _ _ (dom_wtA (κ i))) _ hmem hint
  refine ⟨m', fun k => C.σ₂ (C.d.eF (as k)), fun k => T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (fs k), ?_, ?_, ?_⟩
  · intro k
    refine ⟨C.d.eF (as k), rfl, fun q hq => ?_⟩
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (hla' (as k)).symm.trans_le (has k)
  · intro k
    rw [hbelow]
    refine ⟨fs k, ⟨(cusp_le_sec _ _ _ _ _ (hfs k).1), holSub0_of_cusp D T _ _ _ (fs k) (hfs k).1, ?_⟩, rfl⟩
    intro q hq v hv
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (_root_.GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg _ _ _ _ _ _ _ (fs k)).1 (hfs k).2 v hv
  · rw [hsum]
    have e := _root_.GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC D T _ T.σ₀ C hU.2.2.1 (wtA (κ i)) (κ i).n m m' x' f as fs (fun b => (hf b).1) hBC
    simp only [hx', hfψ] at e
    exact e

end GlobalTheory.DescLoc
