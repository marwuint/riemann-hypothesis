import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsLow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsRename
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRatOfSameOrb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiCpl1EqZeroOfFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenomNotMemOfPrInt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.Rebase
open ValuativeRel

theorem mem_grpAt_of_bc {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V) (hh : h ∈ GfC V)
    (κ : GL (Fin n) (EF D)) (hκ : finM V hn h = κ.1)
    (hoff : ∀ v, ¬ P v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) κ = 1) : h ∈ GlobalTheory.FinPl.grpAt V P := by
  subst hn
  refine (GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts V P h).2 fun i j => ⟨(GlobalTheory.FinPl.SetCut.mem_GfC_iff_entries V h).1 hh i j, fun w hw => ?_⟩
  have e1 : Formalism.UG.prV (E := D.host.E) w (κ.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun g => g.1 i j) (hoff w hw)
  rw [← hκ, GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at e1
  have e2 : Formalism.UG.prV (E := D.host.E) w (toEAf D ((Formalism.L2.Theta.mt V h - 1) i j)) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_sub, e1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e3 := (GlobalTheory.StabOff.prV_comm w (finPart D ((Formalism.L2.Theta.mt V h - 1) i j))).symm.trans e2
  exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm _ _ _).injective).1 e3

theorem pr_mem_of_intAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P) {x : D.host.E}
    (hx : Formalism.L2.Col.IntAt P x) : q.pr (incA D x) ∈ 𝒪[k] := by
  obtain ⟨r, s, hs, e⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ P.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun h => hs0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have h1 := not_not.1 (mt (GlobalTheory.PhiOneVal.mem_prime_iff_pr_inv_notMem q P hP s hs0).2 hs)
  have e' : x = (r : D.host.E) * (s : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hsE, mul_comm]
    exact e
  rw [e', map_mul, map_mul]
  exact mul_mem (GlobalTheory.LocMod.FullLatFrame.pr_int_mem q r) h1

theorem map_pr_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (h : GA D V) (r : (Fin n → D.host.E) →ₗ[D.host.E] (Fin n → D.host.E))
    (hr : ∀ i j, adAt D.host.F P (finM V hn h i j) = algebraMap D.host.E _ (r (Pi.single j 1) i))
    {Y : Type} [Fintype Y] [DecidableEq Y] (pos : Y → ℕ) (F : GlobalTheory.LocMod.Frame k V.rank Y) (hF : IsStdFr pos F) (e : Y ≃ Fin n)
    (he : GlobalTheory.SymBridge.IsOrd pos e) :
    (Formalism.L2.Theta.mt V h).map q.pr = F.β * GlobalTheory.SymBridge.toLoc (q.pr.comp (incA D)) e e r * F.γ := by
  subst hn
  obtain ⟨e', he', hF⟩ := hF
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  refine Matrix.ext fun c d => ?_
  obtain ⟨c, rfl⟩ := e.surjective c
  obtain ⟨d, rfl⟩ := e.surjective d
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std _ e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e hF]
  have h1 := hr (e c) (e d)
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at h1
  exact GlobalTheory.SplitProj.pr_eq_of_adAt q P hP _ _ h1

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) :
    Function.Surjective (toHom S T hS hT) := fun x =>
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' x), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

open Formalism.L2.Col GlobalTheory.StepData GlobalTheory.SymBridge

theorem disjoint_vT (hI : I.Ok) (u : B.Word) (b : I.ι) : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup b)) := by
  refine Finset.disjoint_left.2 fun P h1 h2 => ?_
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h3 := (GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup b) u hX hPr hI.sel_ok
    (hI.T_mem u) hI.g_mem P (Finset.mem_union_left _ h1)).2.2.2.2 h1
  refine GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P ?_ ?_
  · rcases Finset.mem_union.1 h2 with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (I.Q_subset_SQ b h)
  · show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.asIdeal
    rw [map_natCast]
    exact h3

set_option maxHeartbeats 1000000 in

theorem dead_moved (hI : I.Ok) {b : I.ι} {Ch₀ Ch : ℕ → Type} {A A' : TwDat I l Z u b Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (hl : A.Live ι)
    (hb : A'.b0 = A.b0) (hne : ∀ i, i + 1 ≠ B.R.m → A'.p0 i = A.p0 i)
    (heq : ∀ i, i + 1 = B.R.m → ∀ β, (A'.p0 i β).1.1.deco = (A.p0 i β).1.1.deco ∧ cosetIn (A'.p0 i β) = cosetIn (A.p0 i β)) :
    A'.Live ι := by
  refine ⟨hl.inj, hl.first, hl.last, fun j hj γ hγ α z => ?_⟩
  by_cases h1 : j + 1 = B.R.m
  · refine absurd ?_ hγ
    have : ∀ k, k = B.R.m → Function.Surjective (ι k) := by
      rintro _ rfl
      exact hl.last
    exact this _ h1 γ
  by_cases h2 : j + 2 = B.R.m
  swap
  · have h := hl.dead j hj γ hγ α z
    unfold TwDat.xi at h ⊢
    rw [hb, hne j h1, hne (j + 1) h2]
    exact h
  have hL : (I.idx b).Ok I.Ch I.sel (I.tup b) (I.cst b) I.glob j := by
    have := hI.idx_ok b
    rwa [show B.R.m - 2 = j by omega] at this
  obtain ⟨hd, hc⟩ := heq (j + 1) h2 γ
  have key := GlobalTheory.CplDead.xiCpl1_eq_zero_of_frames I.Ch I.sel (I.tup b) (I.cst b) (I.idx b) I.glob j hL u (disjoint_vT hI u b)
    ((A.b0 j α).get (by omega)) (A.p0 j α).1.1 (A.p0 (j + 1) γ).1.1 (A'.p0 (j + 1) γ).1.1 (A.p0 (j + 1) γ).1.2 (A'.p0 (j + 1) γ).1.2 hd
    (GlobalTheory.AdForm.Rebase.repY_cong h2 _ _ hc) (fun x => ?_)
  · unfold TwDat.xi
    rw [hb, hne j h1]
    unfold xiAt
    rw [dif_neg (by omega), dif_pos h2]
    exact (congrArg B.embLL (key _)).trans (map_zero _)
  · obtain ⟨z', hz'⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) x
    have h := hl.dead j hj γ hγ α z'
    unfold TwDat.xi xiAt at h
    rw [dif_neg (by omega), dif_pos h2] at h
    subst hz'
    exact (map_eq_zero_iff _ B.embLL.injective).1 h

end GlobalTheory.Fam.Rebase

namespace GlobalTheory.Fam
end GlobalTheory.Fam

end
