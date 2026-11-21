import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFourSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEqTrace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open GlobalTheory.ThK GlobalTheory.KSplit

noncomputable section

namespace GlobalTheory.LinWSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem pairM_comm {K : Type} [CommRing K] {n d : ℕ} (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM P Q = GlobalTheory.FlipMatch.pairM Q P := by
  simp only [GlobalTheory.FlipMatch.pairM, mul_comm]

theorem pairM_chart {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM ((b⁻¹).1 * P * (c⁻¹).1ᵀ) (-(b.1ᵀ * A * Q * Bᵀ * c.1)) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  first
  | exact @_root_.GlobalTheory.PairingTraceExpansion.main
  | exact _root_.GlobalTheory.PairingTraceExpansion.main
  | (apply _root_.GlobalTheory.PairingTraceExpansion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PairingTraceExpansion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PairingTraceExpansion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PairingTraceExpansion.main ..)

theorem sum_four_swap_pairs_alt {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  first
  | exact @_root_.GlobalTheory.FourTermSumSwap.sum_four_swap
  | exact _root_.GlobalTheory.FourTermSumSwap.sum_four_swap
  | (apply _root_.GlobalTheory.FourTermSumSwap.sum_four_swap <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourTermSumSwap.sum_four_swap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourTermSumSwap.sum_four_swap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourTermSumSwap.sum_four_swap ..)

theorem piW_cA {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (w : AE F E) :
    piW τ (cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_incl {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (e : E) :
    piW τ (inclR (F := F) (AF F) e) = τ e := by
  change GlobalTheory.AdelicU.evFin F v 1 * τ e = τ e
  simp

theorem evFin_symp {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (AE F E))
    (hx : At (evFin F v) x) :
    evFin F v (GlobalTheory.WeilM.symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) =
      GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t b c x) (GlobalTheory.FlipMatch.coY σ X Y t b c u) -
        GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coY σ X Y t b c x) (GlobalTheory.FlipMatch.coX t b c u) := by
  have hss := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hz : At (evFin F v) ((-1 : AE F E) * GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F Y.J) x u) := by
    intro r hr
    have h : ∀ i j, r • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx r hr) i) j
      simpa using this
    rw [← mul_smul_comm]
    unfold GlobalTheory.WeilM.hTens
    simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hz, GlobalTheory.LatVac.evFin_liftV]
  rw [pairM_comm (GlobalTheory.FlipMatch.coY σ X Y t b c x), GlobalTheory.FlipMatch.coX, GlobalTheory.FlipMatch.coX, GlobalTheory.FlipMatch.coY,
    GlobalTheory.FlipMatch.coY, pairM_chart, pairM_chart]
  simp only [map_mul, map_neg, map_one, neg_one_mul, GlobalTheory.WeilM.hTens, map_sum, piW_cA, piW_incl,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hss, AlgHom.comp_apply, hX, hY]
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_neg]
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem locCo_form {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

theorem locCo_eq_zero {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) (M : Model σ X Y) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (t : E →ₐ[F] Fv F v) (z : Matrix (Fin n) (Fin d) (AE F E)) (hz : At (evFin F v) z)
    (h0 : z.map (piW t) = 0) (h1 : z.map (piW (t.comp σ)) = 0) : GlobalTheory.LatVac.locCo M.co v z = 0 := by
  have hf : ∀ w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
      (GlobalTheory.LatVac.locCo M.co v z).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v z).2 = 0 := by
    intro w
    obtain ⟨u, -, rfl⟩ := locCo_surj M.co v w
    rw [locCo_form, evFin_symp hcm X Y hX hY t 1 1 z u hz]
    simp [GlobalTheory.FlipMatch.coX, GlobalTheory.FlipMatch.coY, h0, h1, GlobalTheory.FlipMatch.pairM]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := hf (0, Pi.single i 1)
    simpa using this
  · have := hf (Pi.single i 1, 0)
    simpa using this

theorem locCo_eq_of {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : ∀ r s, σ (X.J s r) = X.J r s) (hY : ∀ r s, σ (Y.J s r) = -Y.J r s) (M : Model σ X Y) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (t : E →ₐ[F] Fv F v) (u u' : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evFin F v) u) (hu' : At (evFin F v) u')
    (h0 : u.map (piW t) = u'.map (piW t)) (h1 : u.map (piW (t.comp σ)) = u'.map (piW (t.comp σ))) :
    GlobalTheory.LatVac.locCo M.co v u = GlobalTheory.LatVac.locCo M.co v u' := by
  rw [← sub_eq_zero, ← map_sub]
  apply locCo_eq_zero hcm X Y hX hY M t
  · intro r hr
    rw [smul_sub, hu r hr, hu' r hr, sub_zero]
  · rw [Matrix.map_sub _ (map_sub _), h0, sub_self]
  · rw [Matrix.map_sub _ (map_sub _), h1, sub_self]

end GlobalTheory.LinWSplit

namespace GlobalTheory.LinWSplit

end GlobalTheory.LinWSplit
