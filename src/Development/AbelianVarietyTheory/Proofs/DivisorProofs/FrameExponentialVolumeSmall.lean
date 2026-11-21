import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLengthLowerBoundQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThickBerg

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem cpt_mem_dom_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
    cpt X x z ∈ X.dom := _root_.GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le

theorem ball_injects : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ (k : U.Comp) (x : Frame (U.X k).Ψ r), IsOrth (U.X k) x →
    100 * (((U.X k).Ψ.card : ℝ) * r) ^ 4 ≤ (l.M' : ℝ) * (U.X k).firstMinimumSq x →
    ∀ γ ∈ (U.X k).Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (nd (U.X k)), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor (U.X k).Ψ r,
      lact γ (cpt (U.X k) x z) = rmul (cpt (U.X k) x z') b → γ = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hl hp hq k x hx hM γ hγ z z' hz hz' b hb he
  obtain ⟨hsd, horb⟩ := _root_.GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf E H Dw l Xo c σ r U hσ hU hl hp hq k
  have hwd : cpt (U.X k) x z ∈ (U.X k).dom := cpt_mem_dom_small E r (U.X k) x z hx hz
  obtain ⟨γ', hγ'U, hγ'c, b', hb', he'⟩ := horb γ hγ _ hwd
  have h1 : lact γ' (cpt (U.X k) x z) =
      rmul (cpt (U.X k) x z') (rmul b (ExtFPf.invF (U.X k) b')) := by
    have e1 := congrArg (fun w => rmul w (ExtFPf.invF (U.X k) b')) (he'.symm.trans he)
    simp only [ExtFPf.rmul_assoc, ExtFPf.rmul_invF _ hb', ExtFPf.rmul_oneF] at e1
    exact e1
  have hγ'1 : γ' = 1 := GlobalTheory.T.deep_congruence_element_separates_chart_ball_thick_frame E r (U.X k) l.M' x hsd hx hM γ' hγ'U hγ'c z z' hz hz' _
    (ExtFPf.mul_mem _ hb (ExtFPf.invF_mem _ hb')) h1
  subst hγ'1
  rw [FundSetPf.lact_one] at he'
  exact (U.X k).Γ_free γ hγ _ hwd b' hb' he'

theorem modelWt_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ),
    (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp,
    (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧
    (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧
    (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = l1 u1 ∧
    (U.X k).Ψ.card = Nat.card (Psi H) := _root_.GlobalTheory.ModelWtGap.model_weight_gap_l1_card

theorem orth_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (y : Frame X.Ψ r), y ∈ X.dom → ∃ x, IsOrth X x ∧ X.firstMinimumSq x = X.firstMinimumSq y ∧
    ∀ P ∈ X.SS la, P x ≠ 0 → P y ≠ 0 ∧ X.pnorm la P y = X.pnorm la P x := by
  intro E _ _ _ r X la y hy
  obtain ⟨x, hx, b, hb, rfl⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r X y hy
  have hxd := ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom X hx
  refine ⟨x, hx, (firstMinimumSq_rightBorel X hxd hb).symm, fun P hP hPx =>
    ⟨?_, FrameDegreeData.pnorm_rmul X la P hP.1.1.2.1 x hxd b hb⟩⟩
  rw [hP.1.1.2.1 x hxd b hb]
  refine mul_ne_zero ?_ hPx
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular ((ExtFPf.upper_iff X b τ).mp (hb τ).2)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)

theorem nums (a l C0 PP T D b uE : ℝ) (ha : 1 ≤ a) (hl : 10 ≤ l) (hlC : C0 ≤ l) (hPP : (a * l) ^ 12 ≤ PP)
    (hT : (a * l) ^ 24 ≤ T) (hD : 1 ≤ D) (hrows : PP * T * D ^ 2 * l ≤ b) (hbu : b ≤ uE) :
    T * a ^ 8 ≤ uE ∧ C0 * a ^ 8 ≤ T ∧ 100 * a ^ 4 ≤ b := by
  have h1 : 1 ≤ a * l := by nlinarith
  have hal8 : a ^ 8 ≤ (a * l) ^ 12 :=
    calc a ^ 8 ≤ (a * l) ^ 8 := pow_le_pow_left₀ (by linarith) (by nlinarith) 8
      _ ≤ (a * l) ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have hPP' : a ^ 8 ≤ PP := hal8.trans hPP
  have hT1 : 1 ≤ T := (one_le_pow₀ h1).trans hT
  have hPP0 : 0 ≤ PP := (by positivity : (0 : ℝ) ≤ a ^ 8).trans hPP'
  have hDl : 1 ≤ D ^ 2 * l := by nlinarith [one_le_pow₀ (n := 2) hD]
  have hTPP : T * PP ≤ b := by
    have h2 : T * PP ≤ PP * T * D ^ 2 * l := by
      have h3 : 0 ≤ PP * T := mul_nonneg hPP0 (by linarith)
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc T * a ^ 8 ≤ T * PP := mul_le_mul_of_nonneg_left hPP' (by linarith)
      _ ≤ uE := hTPP.trans hbu
  · have h4 : a ^ 8 * l ≤ (a * l) ^ 24 := by
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ ha (by norm_num)) (le_self_pow₀ (by linarith) (by norm_num))
        (by linarith) (by positivity)
    have h5 : C0 * a ^ 8 ≤ l * a ^ 8 := mul_le_mul_of_nonneg_right hlC (by positivity)
    linarith
  · have h12 : 100 * a ^ 4 ≤ (a * l) ^ 12 := by
      rw [mul_pow]
      have h6 : (100 : ℝ) ≤ l ^ 12 :=
        calc (100 : ℝ) ≤ 10 ^ 12 := by norm_num
          _ ≤ l ^ 12 := pow_le_pow_left₀ (by norm_num) hl 12
      have h7 : a ^ 4 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
      have h8 : 0 ≤ a ^ 4 := by positivity
      nlinarith
    have h9 : PP ≤ T * PP := le_mul_of_one_le_left hPP0 hT1
    linarith

end GlobalTheory.ThickBerg
