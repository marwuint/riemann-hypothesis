import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelChainLevelPrimeOperatorToStepZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsStepZeroScaleNorms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdForm GlobalTheory.AdForm.RdVal
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop.LComm

variable {D : D7}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a : GA D V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, -, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ?_⟩
  have e2 := congrArg Subtype.val e
  have e3 := congrArg Units.val e2
  exact e3

set_option maxHeartbeats 2000000 in

theorem rdS_inj (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (ψ ψ' : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ)
    (h : ∀ y, rdS θ V hn S yc ψ y = rdS θ V hn S yc ψ' y) : ψ = ψ' := by
  funext c z
  obtain ⟨g, hg⟩ := exists_finM V hn (yc c)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    refine ⟨(c, 1, 1), Subgroup.one_mem _, ?_⟩
    simp [hg]
  have hp := hex.choose_spec
  have hc : hex.choose.1 = c := by
    apply hbij.1
    refine (DoubleCoset.eq _ _ _ _).mpr ?_
    have hr : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        ratPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      Subgroup.mem_map.mpr ⟨_, hp.1, rfl⟩
    have hk : hex.choose.2.2.1 ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      ((S.U_eq _).1 hex.choose.2.2.2).1
    have he : (yc c).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 * (yc hex.choose.1).1 *
        hex.choose.2.2.1 := Units.ext (hg.symm.trans hp.2)
    have hγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      have : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 =
          (yc c).1 * (hex.choose.2.2.1)⁻¹ * ((yc hex.choose.1).1)⁻¹ := by rw [he]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (yc c).2 (Subgroup.inv_mem _ hk)) (Subgroup.inv_mem _ (yc _).2)
    exact ⟨⟨_, hγ⟩, Subgroup.mem_subgroupOf.mpr hr, ⟨_, hk⟩, Subgroup.mem_subgroupOf.mpr hex.choose.2.2.2, Subtype.ext he⟩
  set A : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ with hA
  have hAu : ∀ τ, IsUnit (A τ).det := by
    intro τ
    rw [hA, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)
  have hy : ∀ τ, IsUnit ((A τ)⁻¹ * z.1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ (hAu τ)).mul (z.2 τ)
  have key := congrFun (h ⟨fun τ => (A τ)⁻¹ * z.1 τ, hy⟩) g
  have hz : (fun τ => atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * ((A τ)⁻¹ * z.1 τ)) = z.1 := by
    funext τ
    show A τ * ((A τ)⁻¹ * z.1 τ) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hAu τ), Matrix.one_mul]
  unfold rdS at key
  rw [dif_pos hex, dif_pos hex] at key
  dsimp only at key
  rw [hz, atFr, atFr, dif_pos z.2, dif_pos z.2, hc] at key
  exact mul_left_cancel₀ (Units.ne_zero _) key

theorem chart0_inj {u : D.what₂.Word} (F : Forms0 D u) (θ : InfFam D) (ψ ψ' : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (h : ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ ψ y = (GlobalTheory.Core.Mi.chart0 F).rd θ ψ' y) : ψ = ψ' := by
  have := rdS_inj θ (D.sp.X 0) (rankN D 0 (Nat.zero_le _)) F.cls0.lev F.cls0.y F.cls0.y_bij
    (fun c z => ψ c (F.val0.eY.symm z)) (fun c z => ψ' c (F.val0.eY.symm z)) (fun y => by
      have := h (F.val0.eY.symm y)
      unfold Chart.rd at this
      rw [show (GlobalTheory.Core.Mi.chart0 F).eY (F.val0.eY.symm y) = y from F.val0.eY.apply_symm_apply y] at this
      exact this)
  funext c y
  have h2 := congrFun (congrFun this c) (F.val0.eY y)
  simpa using h2

theorem iter_equiv {M β : Type} [NormedAddCommGroup M] [Module ℂ M] (S : β → M ≃ₗ[ℂ] M) (r : β → ℝ) (hr : ∀ b, 0 < r b)
    (hS : ∀ b φ, ‖S b φ‖ = r b * ‖φ‖) (ε : ℕ → β) (n : ℕ) :
    ∃ (A : M ≃ₗ[ℂ] M) (a : ℝ), 0 < a ∧ (∀ φ, ‖A φ‖ = a * ‖φ‖) ∧ ∀ φ, A φ = GlobalTheory.SeeSaw.iterS (fun b => S b) ε n φ := by
  induction n with
  | zero => exact ⟨LinearEquiv.refl ℂ M, 1, one_pos, fun φ => by simp, fun φ => rfl⟩
  | succ n ih =>
    obtain ⟨A, a, ha, h1, h2⟩ := ih
    refine ⟨A.trans (S (ε (2 * n))), r (ε (2 * n)) * a, mul_pos (hr _) ha, fun φ => ?_, fun φ => ?_⟩
    · rw [LinearEquiv.trans_apply, hS, h1, mul_assoc]
    · rw [LinearEquiv.trans_apply, h2]; rfl

theorem iterS_comm {α α' β : Type} (S : β → α → α) (S' : β → α' → α') (j : α → α') (h : ∀ b x, S' b (j x) = j (S b x))
    (ε : ℕ → β) (n : ℕ) (x : α) : GlobalTheory.SeeSaw.iterS S' ε n (j x) = j (GlobalTheory.SeeSaw.iterS S ε n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show S' _ (GlobalTheory.SeeSaw.iterS S' ε n (j x)) = j (S _ (GlobalTheory.SeeSaw.iterS S ε n x))
    rw [ih, h]

end GlobalTheory.MiTop.LComm
end

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

