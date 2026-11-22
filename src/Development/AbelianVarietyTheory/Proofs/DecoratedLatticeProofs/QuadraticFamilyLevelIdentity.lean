import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevOfMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateCompactMemLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.RowLevel

theorem rTrans_lev {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (G) (hG : G ∈ MultT θ M J χ) (w) {a b k : GA D V} (ha : a ∈ GinfC V)
    (hk : k ∈ GfC V) (hm : b⁻¹ * k * b ∈ J) :
    rTrans k (rTrans (a * b) (G w)) = χ (b⁻¹ * k * b) • rTrans (a * b) (G w) := by
  have h1 := (GlobalTheory.ValMoveProof.valMove D θ hθ V S M J χ).1 G hG w _ hm
  have hc : a * k = k * a := GlobalTheory.AdelicSplit.commute_GinfC_GfC V ha hk
  funext y
  have h2 := congrFun h1 (y * (a * b))
  simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [← h2]
  refine congrArg (G w) ?_
  calc y * k * (a * b) = y * (k * a) * b := by group
    _ = y * (a * k) * b := by rw [hc]
    _ = y * (a * b) * (b⁻¹ * k * b) := by group

theorem rightTranslate_level_conj_acts_by_character_finite {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (G) (hG : G ∈ MultT θ M J χ) (w) {b k : GA D V}
    (hk : k ∈ GfC V) (hm : b⁻¹ * k * b ∈ J) :
    rTrans k (rTrans b (G w)) = χ (b⁻¹ * k * b) • rTrans b (G w) := by
  have := rTrans_lev hθ M J χ G hG w (a := 1) (Subgroup.one_mem _) hk hm
  simpa only [one_mul] using this

theorem conj_mem_off {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} {M : ℕ}
    (hβ : IsSDFrame V β Λ M) (hN : IsSelfDualC V N) (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P (PP.under (𝓞 D.host.F))) {b κ : GA D V} (hb : b ∈ GfC V)
    (hmv : ∀ p, P p → GlobalTheory.FinPl.Moves V b Λ N (· = p)) (hκ : GlobalTheory.FinPl.InK V N P κ) :
    b⁻¹ * κ * b ∈ levS V β L ∧ levChi V β L (b⁻¹ * κ * b) = 1 := by
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ M hβ
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨hκf, hκS⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ κ).1 hκ.1
  have h1 : ∀ p, ¬ P p → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram p (b⁻¹ * κ * b) = 1 := fun p hp => by
    rw [map_mul, map_mul, hκS p hp, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have hSt : Lev.finE V (b⁻¹ * κ * b) ∈ St β := by
    refine (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hfr _).2 fun p => ?_
    by_cases hp : P p
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hΛ.1.fg p, GlobalTheory.StMoves.moves_conj_iff κ (hmv p hp)]
      exact GlobalTheory.LevConj.moves_at_of_moves hN.1 hp hκ.2
    · rw [h1 p hp]; exact one_mem _
  have h' : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Lev.finE V (b⁻¹ * κ * b)) = 1 := fun PP h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (h1 _ (hP PP h))
  refine ⟨⟨(GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hb) hκf) hb,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm V.gram β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hSt h'⟩, ?_⟩
  unfold Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ h', Units.val_one]

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_eq_mu {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E}
    (hPP : PP ∈ L.Pg) (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (π : Lev.EAf D →+* k) (h1 : ∀ a, π (toEAf D a) = q.pr a)
    (h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[k])
    (h4 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation k (π s) < 1)
    (c : ℕ) (hc : c < D.R.m) (μ : kˣ →* ℂˣ) (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta (c + 1)).1⁻¹ μ) (ht : IsTame μ)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (y : (kP PP)ˣ) (x : kˣ) (hy : (y : kP PP) = resS D.host.F PP s)
    (hx : (x : k) = π s) : L.chi (c + 1) PP y = μ x := by
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (y : kP PP)
  have hzP : z ∉ PP.asIdeal := fun hm => y.ne_zero (hz.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
  have hz0 : (z : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hzP (zero_mem _))
  have hπ : π (oToS D.host.F D.host.E z) = q.pr (incA D (z : D.host.E)) := h1 (incA D (z : D.host.E))
  have hv : valuation k (q.pr (incA D (z : D.host.E))) = 1 :=
    le_antisymm (hπ ▸ h3 (oToS D.host.F D.host.E z)) (not_lt.1 fun hl => hzP ((GlobalTheory.LocMod.LevBack.pr_lt q h z).2 hl))
  have hne : q.pr (incA D (z : D.host.E)) ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hd : valuation k ((x : k) - q.pr (incA D (z : D.host.E))) < 1 := by
    have := (h4 (s - oToS D.host.F D.host.E z)).1 (by rw [map_sub, resS_oToS, hz, hy, sub_self])
    rwa [AddSubgroupClass.coe_sub, RingHom.map_sub, hπ, ← hx] at this
  have e1 : μ x = μ (Units.mk0 _ hne) := by
    have := ht (x * (Units.mk0 _ hne)⁻¹) (by
      have e : ((x * (Units.mk0 _ hne)⁻¹ : kˣ) : k) - 1 =
          ((x : k) - q.pr (incA D (z : D.host.E))) * (q.pr (incA D (z : D.host.E)))⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hne]; simp
      rw [e, map_mul, map_inv₀, hv, inv_one, mul_one]
      exact hd)
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have e2 := hμ (Units.mk0 _ hne) (GlobalTheory.LocMod.SplitHecke.idlU q (Units.mk0 _ hne)) rfl
  have e3 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q h (hL.mu0 ⟨c, hc⟩) hz0 (Units.mk0 _ hne) rfl
  have e4 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q h hL.eta hz0 (Units.mk0 _ hne) rfl
  rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := Units.mk0 _ hz0)
    ((PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP), Units.val_one] at e4
  have e5 := hL.chi ⟨c, hc⟩ PP hPP z (Units.mk0 _ hz0) y rfl hz.symm
  rw [← e5] at e3
  have e4' : L.eta (GlobalTheory.LocMod.SplitHecke.idlU q (Units.mk0 _ hne)) = 1 := Circle.coe_injective e4
  apply Units.ext
  rw [e1, e2]
  unfold Lift.chrStep
  split_ifs
  · simp only [MonoidHom.inv_apply, MonoidHom.mul_apply, e4', inv_one, mul_one, Circle.coe_inv]
    rw [e3]; simp
  · simp only [MonoidHom.inv_apply, Circle.coe_inv]
    rw [e3]; simp

theorem red_lam {s κ t j n r : ℕ} (S : GlobalTheory.SymChain.SymData k s κ) (hr0 : r = κ + (s + 1)) (hr : r ≤ n)
    {e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j ≃ Fin n} (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) {O K : Type} [CommRing O]
    [CommRing K] [Nontrivial K] (φ : O →+* K) (ψ : O →+* k) (h1 : ∀ z, ψ z ∈ 𝒪[k]) (h2 : ∀ z, φ z = 0 ↔ valuation k (ψ z) < 1)
    (χ : ℕ → Kˣ →* ℂˣ) (hχ : ∀ c, c < j → ∀ (z : O) (y : Kˣ) (x : kˣ), (y : K) = φ z → (x : k) = ψ z → χ (c + 1) y = S.μ (c + 1) x)
    (Y : GL (Fin n) O) (g : (S.P.iter (Fin t) S.μ S.tame j).J)
    (hy : ∀ a b, ψ (Y.val (e a) (e b)) = (g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j) k).val a b) :
    Formalism.UG.bc φ Y ∈ blockTri (blkOf r t) ∧ ∃ x : S.P.J, (∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O,
        φ z = (upperLeftBlock hr (Formalism.UG.bc φ Y)).val a' b' → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - ψ z) < 1) ∧
      (S.P.iter (Fin t) S.μ S.tame j).lam g =
        S.P.lam x * ∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) (Formalism.UG.bc φ Y)) := by
  obtain ⟨-, hP⟩ := (GlobalTheory.SymChain.pattern_iter _ _ _ S (Fin t) j g.1).1 g.2
  have hb := (GlobalTheory.LocMod.LevBack.red_of_pattern S hr0 hr he φ ψ h1 h2 Y fun a b hab => by rw [hy]; exact hP a b hab).1
  obtain ⟨g₀, Dm, e0, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k _ (Fin t) S.P S.μ S.tame j g
  refine ⟨hb, g₀, fun a b a' b' ha hb' z hz => ?_, ?_⟩
  · have hc : ∀ a (a' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → Fin.castLE hr a' = e (Sum.inl a) := fun a a' h =>
      Fin.ext (by rw [he]; rcases a with a | a <;> exact h)
    rw [upper_block_val_submatrix hr (blockTri_blkOf_le _ _ hb), submatrix_apply, hc a a' ha, hc b b' hb'] at hz
    rw [e0, submatrix_apply, ← hy, ← map_sub, ← h2, map_sub, hz]
    exact sub_self _
  · rw [el, Finset.prod_range]
    congr 1
    refine Finset.prod_congr rfl fun c _ => (hχ c c.2 (Ix.diagonalBlockOfMatrix (Y.val.submatrix e e) c).det _ _ ?_ ?_).symm
    · have hk := GlobalTheory.LocMod.LevBack.blkOf_zPos hr0 he
      have hbij : Function.Bijective fun i : Fin t =>
          (⟨e (.inr (c, i)), hk _⟩ : {i : Fin n // blkOf r t i = c.val + 1}) := by
        refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
        obtain ⟨i | ⟨c', s⟩, rfl⟩ := e.surjective i
        · exact absurd ((hk _).symm.trans hi) (Nat.succ_ne_zero _).symm
        · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((hk _).symm.trans hi))
          exact ⟨s, rfl⟩
      rw [diag_block_det_val _ hb, ← det_submatrix_equiv_self (Equiv.ofBijective _ hbij), RingHom.map_det]
      rfl
    · rw [Matrix.GeneralLinearGroup.val_det_apply, (hD c).2, RingHom.map_det]
      congr 1
      ext a b
      exact (hy _ _).symm

end Loc

theorem mat_frame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (π : Lev.EAf D →+* k) (h1 : ∀ a, π (toEAf D a) = q.pr a) {V : HSp D}
    {β : GL (Fin V.rank) (Lev.EAf D)} {b x : GA D V} {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k V.rank Y) (L : LatFrame k ι Y) (e : ι ≃ Fin V.rank)
    (hmv : MovedTo (ofSplit q) V b β ((F.β * L.bas.val).submatrix id fun i => L.ord (e.symm i))) (xk : GL Y k)
    (hx : (mt V x).map q.pr = F.β * xk.val * F.γ) :
    GeneralLinearGroup.map π (β⁻¹ * Lev.finE V (b⁻¹ * x * b) * β) = reGL e (L.conj.symm xk) := by
  have hmap : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (AE D), (M.map (toEAf D)).map π = M.map q.pr :=
    fun M => Matrix.ext fun _ _ => h1 _
  rw [← GlobalTheory.LocMod.LevBack.conj_frame F L e (GeneralLinearGroup.map π (Lev.finE V b * β))
    (GeneralLinearGroup.map π (Lev.finE V x)) (L.conj.symm xk) ?_ ?_]
  · rw [MonoidHom.map_mul (Lev.finE V), MonoidHom.map_mul (Lev.finE V), MonoidHom.map_inv, GlobalTheory.LocMod.LevBack.conj_conj,
      MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  · have hb : (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map (toEAf D) = β.val :=
      Matrix.ext fun _ _ => GlobalTheory.LocMod.LevBack.toEAf_finEmb _
    refine Eq.trans ?_ (hmv _ hb)
    refine Eq.trans ?_ (hmap _)
    rw [Matrix.map_mul, hb]
    rfl
  · rw [MulEquiv.apply_symm_apply]
    exact (hmap _).trans hx

theorem conj_list_prod {G ι : Type} [Group G] (b : G) (h : ι → G) (l : List ι) :
    b⁻¹ * (l.map h).prod * b = (l.map fun i => b⁻¹ * h i * b).prod := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← ih]; group

end GlobalTheory.RowLevel
