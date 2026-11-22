import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSixthOfEarlier
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingBottomRowOrbits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralAbsoluteConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralUnfolded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThird
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMixedToEuclideanConjSqRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeAbsNormUnitsPrimeIdealUnit
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspidality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero

private theorem norm_sq_of_scaled (k p : ℕ) (hk : 3 ≤ k) (hp : 2 ≤ p) (x : ℂ)
    (h : ‖x * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = (p : ℝ)) : ‖x‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hr : (0 : ℝ) < (p : ℝ) ^ (1 - (k : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow] at h
  have hr2 : ((p : ℝ) ^ (1 - (k : ℝ) / 2)) ^ 2 = (p : ℝ) ^ (2 - (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have he : (((k - 1 : ℕ) : ℝ)) + (2 - (k : ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hkey : (p : ℝ) ^ (k - 1) * (p : ℝ) ^ (2 - (k : ℝ)) = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0, he, Real.rpow_one]
  have hne : (p : ℝ) ^ (2 - (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  rw [hr2] at h
  exact mul_right_cancel₀ hne (h.trans hkey.symm)

theorem UpperTheory.V.Z.Sym.Unl.badAbs :
    UpperTheory.V.Z.Sym.Unl.BadAbs := by
  intro k N _ hk χ hχ g p hp hpN
  have b0 : Ad3.R.B0 := @_root_.GlobalTheory.CompanionTheory.RankinQ.b0
  have c0 : Ad3.R.C0 := @_root_.GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant
  have c1 : Ad3.R.C1 := @GlobalTheory.T.congruence_subgroup_coset_decomposition
  have u2 : Ad3.R.U2 := @_root_.GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char
  have g0 : Ad3.R.G0 := @_root_.GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain (@_root_.GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain)
  have g1 : Ad3.R.G1 := @_root_.GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing (@_root_.GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts)
  have f0 : Ad3.R.F0 := @_root_.GlobalTheory.CompanionTheory.RankinSelbergQ.f0 b0
  have f0b : Ad3.R.F0b := @_root_.GlobalTheory.CompanionTheory.NewformLiftConductor.f0b b0
  have f1 : Ad3.R.F1 := @GlobalTheory.T.newform_lift_level b0
  have f1b : Ad3.R.AutomorphicLevelEquivariance := @_root_.GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance b0
  have f2 : Ad3.R.F2 := @_root_.GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift
  have f3a : Ad3.R.HeckeSumLocalTranslates := @_root_.GlobalTheory.CompanionTheory.RSq.f3a b0
  have f3 : Ad3.R.F3 := @_root_.GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift b0 c0 c1 f0b f1 f1b f3a
  have f5 : Ad3.R.F5 := @_root_.GlobalTheory.CompanionTheory.NewformLiftDecay.main b0
  have f4 : Ad3.R.F4 := @_root_.GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq b0 c1 u2 g0 g1 f0b f1 f2 f3 f5
  obtain ⟨hform, heig⟩ := Ad3P.sEig k N hk χ g
  obtain ⟨ω, hω⟩ := f0 N χ
  obtain ⟨-, φ, hφ⟩ := f1 k N χ _ _ hform g.one ω hω
  obtain ⟨v, rfl⟩ := b0.2.2.1 p hp
  have h := f4 k N hk χ hχ _ _ hform heig ω φ hω hφ v hpN
  exact norm_sq_of_scaled k _ hk hp.two_le _ h
