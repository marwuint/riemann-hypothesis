import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainAdjointLatticeExchange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRepresentativesHalfQuotientPairingTrivialD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorePairIntegralPointPairsTriviallyHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CosDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cA_cA₀ {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => show a ⊗ₜ[D.host.F] star (star x) = _; rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem latO_le_true {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩

theorem isLatVac_mono {D : D7} {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ' ≤ Λ) {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ f) : IsLatVac hs Λ' f :=
  ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end GlobalTheory.CosDatum

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CosDatum in

theorem datumEx : DatumEx := by
  intro D hq T L μ0 hL sc G W M hM i hi r r' hr hr' S S' MM MM' x₀ hx₀
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hθ : IsInfFam W.θ := W.θ_is
  have hEx : ExchLaw D := _root_.GlobalTheory.ExchPf.exchLaw D
  have hLE : LatExch := _root_.GlobalTheory.LatExchPf.latExch
  have hadj := GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (G.V (.core i)) (G.V (.core (i + 1)))
  obtain ⟨e, he, -⟩ := W.cosVec_is
  obtain ⟨f₀, hf₀⟩ := _root_.GlobalTheory.CoreVacRe.vacExists_reLat D hq T L μ0 hL sc G W M hM i hi r r' S S' MM MM'
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice D hq T L μ0 hL sc G W M hM i hi e he
  have hxi := _root_.GlobalTheory.CoreOnto.IntDatum.psi_int D hq T L μ0 hL sc G W M hM i hi e he x₀ hx₀
  have hhalf : ∀ z ∈ R, IsHalf e (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) := fun z hz => by
    have := hadj.half _ z (hR1 z hz).1
    rwa [cA_cA₀] at this
  have hfin : ∀ z ∈ R, (adjO (G.V (.core i)) (G.V (.core (i + 1))) z).map (infPart D) = 0 := fun z hz =>
    _root_.GlobalTheory.IdemHalf.halfFin _ e he _ (Or.inl (hhalf z hz))
  let c : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ :=
    fun z => W.ψ (-symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) z)
  let f : WO r.sp r'.sp → ℂ :=
    ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) f₀
  have hexs : ∀ g : WO r.sp r'.sp → ℂ,
      exch (G.V (.core i)) (G.V (.core (i + 1)))
        (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) =
      ∑ z ∈ R, c z • heisO W.ψ (G.pS (.core i)) (G.pT (.core i)) z (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
    intro g
    funext x
    have h2 := fun z : WO (G.pS (.core i)) (G.pT (.core i)) =>
      congrFun ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).2.1 z g) x
    show (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g)
      (adjO (G.V (.core i)) (G.V (.core (i + 1))) x) = _
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, h2 z]
    rfl
  have hf₀th : IsThetaFunO W.ψ r.sp r'.sp f₀ := hf₀.2.theta
  have hcomb := _root_.GlobalTheory.CombTheta.comb_theta W.ψ W.θ r.sp r'.sp hψ hθ f₀ hf₀th R c _ hfin
  have hex0 : exch (G.V (.core i)) (G.V (.core (i + 1))) f₀ ≠ 0 := by
    intro h0
    apply GlobalTheory.SeeSaw.Inh.vac_ne_zero hf₀
    funext y
    obtain ⟨x, rfl⟩ := (hEx W.ψ _ _ hψ).2.2.2.1.2 y
    exact congrFun h0 x
  have hRne : ∃ z ∈ R, c z ≠ 0 := by
    obtain ⟨y', hy', -⟩ := hR2 0 (fun _ _ => mul_zero _) (fun u _ => by
      have h00 : symplO (G.pS (.core i)) (G.pT (.core i)) u 0 = 0 := by unfold symplO hO; simp
      rw [h00, AddChar.map_zero_eq_one])
    exact ⟨y', hy', addChar_ne_zero _ _⟩
  refine ⟨f, ⟨hcomb.1, ?_, fun τ => _root_.GlobalTheory.CombFockTranslate.isFockVacAt_comb W.ψ W.θ r.sp r'.sp hψ hθ _ τ f₀ hf₀th (hf₀.2.fock τ) R c _ hfin⟩,
    ?_, fun φ => ?_⟩
  · intro h0
    have h2 : exch (G.V (.core i)) (G.V (.core (i + 1))) f = 0 := by rw [h0]; rfl
    refine _root_.GlobalTheory.HeisJointEigen.sum_heisO_ne_zero W.ψ (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he R hR4
      _ (_root_.GlobalTheory.ExchLatPf.exchLat D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' f₀ hf₀.2.lat) hex0 c hRne ?_
    rw [← hexs f₀]
    exact h2
  · show IsLatVac _ _ _
    refine _root_.GlobalTheory.LatVacComb.isLatVac_sum_heisO W.ψ r.sp r'.sp _ f₀ (isLatVac_mono (latO_le_true _ _ _ _ _) hf₀.2.lat) R c _ ?_
    intro z hz u hu
    rw [_root_.GlobalTheory.OrthOff.orthOff D hq T L μ0 hL sc G W M hM e he r.sp r'.sp _ _ u hu _ (hhalf z hz), AddChar.map_zero_eq_one]
  · have hpt : ptOf W.ψ W.θ MM MM' f φ = ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp
        (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) (ptOf W.ψ W.θ MM MM' f₀ φ) :=
      hcomb.2 (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hfl := _root_.GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO W.ψ W.θ r.sp r'.sp hψ hθ _ _ _ f₀ hf₀th hf₀.2.lat (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hgl := _root_.GlobalTheory.ExchLatPf.exchLat D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' _ hfl.2
    have hth : IsThetaFunO W.ψ r.sp r'.sp (ptOf W.ψ W.θ MM MM' f φ) := by
      rw [hpt]; exact (_root_.GlobalTheory.CombTheta.comb_theta W.ψ W.θ r.sp r'.sp hψ hθ _ hfl.1 R c _ hfin).1
    have hth' := (((_root_.GlobalTheory.ReLatPf.reLatLaw_holds D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r').1 _).1 hth
    have hΦth := ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).1 _).1 hth'
    have hΦ := hexs (ptOf W.ψ W.θ MM MM' f₀ φ)
    rw [← hpt] at hΦ
    rw [hΦ] at hΦth ⊢
    refine ⟨⟨hΦth, _root_.GlobalTheory.LatVacComb.isLatVac_sum_heisO W.ψ _ _ _ _ (isLatVac_mono (Λ' := depLat G (.core i)) (fun u hu => hu.1) hgl) R c (fun z => z)
      (fun z hz => (hR1 z hz).2)⟩, ?_⟩
    intro e' he' y hy hyd
    obtain rfl := _root_.GlobalTheory.IdemSumUniq.idemSum_unique _ _ _ he he'
    exact _root_.GlobalTheory.CosetEigen.cosetSum_eigen W.ψ _ _ (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he (depLat G (.core i)) R _ hR1 hR2 hR3 hxi
      _ hgl y hy hyd

end GlobalTheory.CoreOnto

end
