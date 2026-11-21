import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNegatedSpaceDiscreteSeriesModelTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanish
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowArrow

variable {D : D7}

theorem unit_of_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    IsUnit b.det := by
  have hJ : IsUnit (Formalism.REAL.Jm ε).det := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
  rw [← h, det_mul] at hJ
  exact isUnit_of_mul_isUnit_right hJ

theorem inv_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    (b⁻¹)ᴴ * Formalism.REAL.Jm ε * b⁻¹ = G := by
  have hb := unit_of_gram h
  have h1 : (bᴴ)⁻¹ * bᴴ = 1 := nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hb.star)
  have h2 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  rw [← h, conjTranspose_nonsing_inv]
  calc (bᴴ)⁻¹ * (bᴴ * G * b) * b⁻¹ = ((bᴴ)⁻¹ * bᴴ) * G * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_frame (V : HSp D) (c b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (b τ)ᴴ * gramAt D V τ * b τ = Formalism.REAL.Jm ε ∧ c τ * b τ = b τ * Formalism.REAL.Jm ε) :
    ∃ A : Fr V, A.cart = c ∧ A.onb = b := by
  choose ε hε using h
  refine ⟨⟨ε, fun τ => (b τ)⁻¹, fun τ => isUnit_nonsing_inv_iff.2 ((isUnit_iff_isUnit_det _).2 (unit_of_gram (hε τ).1)),
    fun τ => inv_gram (hε τ).1⟩, ?_, ?_⟩
  · funext τ
    simp only [Fr.cart]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1), ← (hε τ).2, Matrix.mul_assoc,
      mul_nonsing_inv _ (unit_of_gram (hε τ).1), Matrix.mul_one]
  · funext τ
    simp only [Fr.onb]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1)]

theorem lifts_neg {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    (hP : PairLifts D X) (hE : PairEx) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {A B : HSp D} {S S' : D.what₂.Tau → SPar} (MA : DSModel A S) (MB : DSModel B S') {aS aT : D.what₂.Tau → ℚ}
    (hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ) (aS τ) (aT τ)) (FA : Fr A) (FB : Fr B)
    (hA : cart MA = FA.cart) (hB : cart MB = FB.cart) {ω : GlobalTheory.Grid.WRep (GlobalTheory.Grid.sgn true B) A}
    (hω : IsWeilExp ψ (GlobalTheory.Grid.sgn true B) A aS aT ω) {f₀ : WO (GlobalTheory.Grid.sgn true B) A → ℂ}
    (hf₀ : IsVacF ψ θ (frSgn true FB) FA f₀) (h0 : f₀ ≠ 0) {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν) :
    ∃ It : PolF D A.rank B.rank → SmT MA → SmT MB, ∀ f, IsVacF ψ θ (frSgn true FB) FA f →
      LiftsM θ MA MB ν 𝓕 (fun P h g => thetaKO ω ((GlobalTheory.Grid.ofSgn true B).symm h) g (ptF ψ θ (frSgn true FB) FA f P)) It := by
  obtain ⟨N, κ, hN⟩ := GlobalTheory.negModel_tr D θ hθ B S' MB
  have cS : ∀ τ, (Fr.ofModel N).cart τ = (frSgn true FB).cart τ := fun τ =>
    (hN.cart τ).trans ((congrArg _ (congrFun hB τ)).trans (cart_frSgn true FB τ).symm)
  have cT : ∀ τ, (Fr.ofModel MA).cart τ = FA.cart τ := fun τ => congrFun hA τ
  have vac : ∀ f, IsVacF ψ θ (frSgn true FB) FA f → IsVacF ψ θ (Fr.ofModel N) (Fr.ofModel MA) f :=
    fun f h => ⟨h.1, fun τ => by rw [cS, cT]; exact h.2 τ⟩
  obtain ⟨j, hj⟩ := GlobalTheory.FrameChange.ptF_frame_change D ψ θ hψ hθ (GlobalTheory.Grid.sgn true B) A _ _ _ _ cS cT
  obtain ⟨It, hIt⟩ := hE D _ S aS aT hR _ A N MA θ ψ hθ
  have hv : IsVacVec ψ θ N MA f₀ := ⟨hf₀.1, h0, (vac f₀ hf₀).2⟩
  refine ⟨fun P v => κ (It (j P) v), fun f hf F hF => ?_⟩
  obtain ⟨F₁, hF₁, e₁⟩ := hP _ _ aS aT (fun τ => GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 (hR τ)) _ A N MA θ ψ hθ ω hω f₀ It hv
    (hIt ω hω f₀ hv) ν 𝓕 hν h𝓕 f (vac f hf) F hF
  obtain ⟨F', hF', e'⟩ := hN.mult' F₁ hF₁
  refine ⟨F', hF', fun P v h => ?_⟩
  have := e₁ (j P) v ((GlobalTheory.Grid.ofSgn true B).symm h)
  rw [← ptF_ofModel, e'] at this
  simp only [hj f hf.1 P, MulEquiv.apply_symm_apply, RingHom.id_apply] at this
  exact this

theorem cen_eq (τ : D.what₂.Tau) : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
  funext i
  unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
  rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
  rfl

theorem parRow_eq (i : ℕ) (τ : D.what₂.Tau) : parRow D 1 i τ = GlobalTheory.Grid.parV D i 0 τ := by
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [cen_eq, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [GlobalTheory.Grid.parV, hg]
  rfl

theorem exp_att {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {c : ℚ} (h : HasInfExp D χ τ c)
    (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) : HasInfExp D (Lift.attChr χ η n) τ (att c n) := by
  unfold Lift.attChr att
  split_ifs
  · rw [sub_eq_add_neg]
    exact StepVac.hasInfExp_mul h (StepVac.hasInfExp_inv hη)
  · exact h

end GlobalTheory.RowArrow

end
