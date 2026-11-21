import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardCompUnfLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHost
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PrincipalDatumFgPerfectTracePairing
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_card_comp_le : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * Zb D large₂ ^ 2 := by
  intro D T h large₂ j hj w hP h2 hrn h16 σ hσ
  obtain ⟨hg, hlrd, hd, hcc, hf, -, -, -, hn⟩ := hP
  obtain ⟨-, -, -, -, -, hfd, hdE, -, -, -, hsk, hne, -⟩ := _root_.GlobalTheory.HostClear.host_clear D large₂.sc.L h2 hlrd hd hcc
  obtain ⟨AA, hFG, hA, hdual⟩ := _root_.GlobalTheory.principalDatum_trace_perfect D
  obtain ⟨-, -, hM, -, -, -, hJ⟩ := _root_.GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hrL : Real.log D.R.r ≤ large₂.sc.L :=
    le_trans (Real.log_le_log (by exact_mod_cast hr) (by exact_mod_cast hrn)) hn
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    rcases Nat.eq_zero_or_pos (D.host.g 0) with a | a
    · rw [a]; simp; linarith
    rcases Nat.eq_zero_or_pos (D.host.g 1) with b | b
    · rw [b]; simp; linarith
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le _root_.GlobalTheory.QNorm.hasseNormSt _root_.GlobalTheory.thetaUnifAV_all GlobalTheory.T.abelianScheme_laws_unconditional.1 D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    D.host.xi0 AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact_mod_cast h16) h2 hdE hrL
    (by rw [hfd]; exact_mod_cast hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.RunIn
