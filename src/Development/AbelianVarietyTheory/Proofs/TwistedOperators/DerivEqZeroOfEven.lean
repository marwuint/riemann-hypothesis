import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanSquareNormWeilRepSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAway
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamily
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelCoordinatesBijOnAndWeilLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitution
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMatrixCoefficientEven
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumOneParameterGeneratorCommutators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensorStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem unitary (D : D7) : Unitary D := by
  intro ψ S T χS χT om hW
  have hstd := hW.std
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨⟨(μ₀, 𝓕₀), h₀⟩, fun q hq f₁ f₂ hf₁ hf₂ => ?_⟩
  have L := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T q.1 q.2 hstd hq f₁ f₂ hf₁ hf₂
  refine ⟨fun c => GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul c hf₁) hf₂, L.1, L.2.2.2.2.2.1,
    L.2.2.2.2.2.2.2, fun w => ⟨?_, (L.2.2.2.2.2.2.1 w).1⟩, fun p => ⟨hW.om_pres p f₁ hf₁, ?_⟩,
    _root_.GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub D ψ S T χS χT om q.1 q.2 hW hq f₁ f₂ hf₁ hf₂⟩
  · exact (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₁ hf₁
  · exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW q.1 q.2 hq p f₁ f₂ hf₁ hf₂

theorem restrictedTensor (D : D7) : RestrictedTensor D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  have hstd := base_std hB
  have hinf := base_inf hB
  refine ⟨fun p f hf => ⟨((_root_.GlobalTheory.PlaceStable.heis_stable D ψ θ S T sS sT ΛS ΛT hstd hinf f hf.1).2 p hf).1,
      _root_.GlobalTheory.LocalFactorUnitary.isLocal_om_gAt D ψ θ S T χS χT om sS sT ΛS ΛT hW hinf p f hf⟩,
    fun x hx => _root_.GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x hx, fun f hf ε hε => ?_,
    fun x f hx => ⟨fun w => GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w,
      fun g h => _root_.GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x f hx g h⟩⟩
  obtain ⟨f', hf', hlt⟩ := _root_.GlobalTheory.HeisDense.span_translates_dense D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ f hf ε hε
  refine ⟨f', Submodule.span_mono ?_ hf', hlt⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨_, GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ (fun _ => f₀) f₀
    (_root_.GlobalTheory.LocalPure.isPure_base_and_local D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1 w⟩

theorem coeffProduct (D : D7) : CoeffProduct D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ x₂ f₂ h₁ h₂ g h
  exact _root_.GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ x₂ _ f₂
    (_root_.GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ h₁ g h) h₂

theorem cA_cA {D : D7} {e : AE D} {p : Place D} (h : e + cA D e = idem D p) : cA D (cA D e) = e := by
  have hp : cA D (idem D p) = idem D p := (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.2.1 p
  have h2 : cA D e + cA D (cA D e) = cA D e + e := by
    rw [← map_add, h, hp, ← h, add_comm]
  exact add_left_cancel h2

theorem isSplitIdem_cA {D : D7} {e : AE D} {p : Place D} (he : IsSplitIdem D e) (h : e + cA D e = idem D p) :
    IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, hε⟩ := he
  have hcc := cA_cA h
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [hcc, mul_comm, h2]
  · rw [hcc, add_comm, hε]

theorem splitModel (D : D7) : SplitModel D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := _root_.GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  refine ⟨(_root_.GlobalTheory.PlaceModelOnto.placeModel_onto_local D ψ θ S T sS sT ΛS ΛT f₀ hB v e he.1 he.2.1).1, fun Tm hTm => ?_⟩
  have M := _root_.GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e e he.1 he.2.1 (Or.inl rfl)
    T.rank S.rank (mapCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalf_eq_pull]
  exact ⟨M.1, fun ν hν => _root_.GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v e he.1 T.rank S.rank
    (mapCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ S BS g) (grpCo φ T BT h) (fun t => hC.2 g h t) Φ hΦ⟩

theorem splitModelAdj (D : D7) : SplitModelAdj D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := _root_.GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hs : IsSplitIdem D (cA D e) := isSplitIdem_cA he.1 he.2.1
  have hsum : cA D e + cA D (cA D e) = idem D (.inl v) := by
    rw [cA_cA he.2.1, add_comm]
    exact he.2.1
  refine ⟨(_root_.GlobalTheory.PlaceModelOnto.placeModel_onto_local D ψ θ S T sS sT ΛS ΛT f₀ hB v (cA D e) hs hsum).1, fun Tm hTm => ?_⟩
  have M := _root_.GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e (cA D e) he.1 he.2.1 (Or.inr rfl)
    S.rank T.rank (adjCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalfAdj_eq_pull]
  exact ⟨M.1, fun ν hν => _root_.GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v (cA D e) hs S.rank T.rank
    (adjCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ T BT h) (grpCo φ S BS g) (fun t => hC.2 g h t) Φ hΦ⟩

theorem deriv_eq_zero_of_even {c : ℝ → ℂ} {a : ℂ} (h : HasDerivAt c a 0) (he : ∀ t, c (-t) = c t) : a = 0 := by
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id' (0 : ℝ)).neg
  have h0 : HasDerivAt c a (-(0 : ℝ)) := by rwa [neg_zero]
  have h1 := h0.scomp (0 : ℝ) hn
  have h2 : (c ∘ fun t : ℝ => -t) = c := funext fun t => he t
  rw [h2] at h1
  have h3 := h.unique h1
  rw [neg_one_smul] at h3
  linear_combination h3 / 2

private theorem exists_conj_mul_eq_mul {ι : Type*} {n : ℕ} (C C' : ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i, C i * C' i = 1)
    (s B : ι → Matrix (Fin n) (Fin n) ℂ) :
    ∃ s' B' : ι → Matrix (Fin n) (Fin n) ℂ, (∀ i, s' i * C i = C i * s i) ∧ ∀ i, B' i = C i * B i := by
  refine ⟨fun i => C i * s i * C' i, fun i => C i * B i, fun i => ?_, fun i => rfl⟩
  have h' : C' i * C i = 1 := mul_eq_one_comm.mp (h i)
  simp only [Matrix.mul_assoc, h', Matrix.mul_one]

theorem fockModel (D : D7) : FockModel D := by
  intro ψ θ S T χS χT om hW hθ τ
  obtain ⟨mS, mT, hm⟩ := _root_.GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hW hθ τ
  refine ⟨mS, mT, ?_⟩
  intro sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac P
  have hstd := hW.std
  have hPT : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) := by
    intro Q
    obtain ⟨sS', BS', hS', hBS'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D S)) sS BS
    obtain ⟨sT', BT', hT', hBT'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D T)) sT BT
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS' BS BS' sT sT' BT BT' 1 1
      hS' hT' hBS' hBT' f hf Q).1
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨hPT P, fun μ 𝓕 hμ Q => _root_.GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT
      f hf hvac μ 𝓕 hμ P Q,
    fun κS κT hκS hκT g h hg hh => _root_.GlobalTheory.FockCompact.om_pureTensorO_compact D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT
      hBS hBT f hf τ κS κT hκS hκT g h hg hh _
      (hm sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac κS κT hκS hκT g h hg hh) P,
    fun YS YT hYS hYT w => ?_⟩
  have hL := _root_.GlobalTheory.VacuumEven.coeff_even D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT
  obtain ⟨Gn, hGn⟩ := _root_.GlobalTheory.PlaceTensor.GenPair.exists_generator D ψ θ S T χS χT om hW hθ τ _ hL.1 _ hL.2.1

  have key := _root_.GlobalTheory.FockLieQuad.acts_by_fockP D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT μ₀ 𝓕₀ h₀ Gn
    (fun f' hf' => ⟨(hGn f' hf').1, (hGn f' hf').2.1, (hGn f' hf').2.2.1⟩) f hf hvac
    (fun g hg hgv => deriv_eq_zero_of_even ((hGn f hf).2.2.2.2 μ₀ 𝓕₀ h₀ g hg)
      (fun t => hL.2.2 f g hf hvac hg hgv μ₀ 𝓕₀ h₀ t)) P
  rw [← key]
  exact (hGn _ (hPT P)).2.2.2.1 w

theorem placeModels : ∀ D : D7, PlaceModels D := fun D =>
  ⟨unitary D, restrictedTensor D, coeffProduct D, splitModel D, splitModelAdj D, _root_.GlobalTheory.SplitLatticeHalves.splitLattice D, _root_.GlobalTheory.PlaceTensor.inertVacuumFixed D,
    _root_.GlobalTheory.PlaceTensor.splitVacuumFixed D, fockModel D, _root_.GlobalTheory.FockPureTensor.fockPure D, _root_.GlobalTheory.AdjVecLocal.thetaVecLocal D, GlobalTheory.T.thetaChainStepVector_localPureTensor D⟩

end GlobalTheory.PlaceTensor
