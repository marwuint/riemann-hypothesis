import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutEnd2OfAutPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Across2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentImagQuadratic

open private kills_pow pairing2 from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentImagQuadratic
open private kills_open exists_two flag det_one sq_of_trace norm_lt' cont_val cont_of_open irr_sub comm_mem isIrr_of tw_tw det_star conj_mat from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutEnd2OfAutPt
open UpperTheory.GalN.V

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

open UpperTheory.V.Z.Win UpperTheory.V.Z

private theorem detAlg (H : Af.HypothesesH) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {W : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hW : Continuous W) {M : ℕ} (hM : 1 ≤ M) (hχ : Af.KillsMu M (Matrix.GeneralLinearGroup.det.comp W)) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  refine (Af.algOfCyc H ℚ Ω l ι).1 _ (Matrix.GeneralLinearGroup.continuous_det.comp hW) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩

private theorem polTwo {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W)) (c : G ℚ Ω)
    (hc : Sd.IsCC c) : Af.Sol.Pol ι (W.comp (Base.galEmb ℚ K Ω)) := by
  obtain ⟨Q, hQ⟩ := pairing2 W c
  exact ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, c, Q, h,
    Ws.auSign _, hc, fun s s' h => by
      have h' : Base.galEmb ℚ K Ω s' = c * Base.galEmb ℚ K Ω s * c⁻¹ := h
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
      exact hQ _ _ rfl⟩

