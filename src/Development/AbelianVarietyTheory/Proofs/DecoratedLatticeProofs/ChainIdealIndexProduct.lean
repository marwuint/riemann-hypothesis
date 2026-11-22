import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolumeSeeSawTupleLevelEqSphericalDivIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdLocalParts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.StepConst

variable {D : D7}

theorem local_part {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) :
    ∃ c : GA D V, SuppAt q.e V c ∧ (mt V c).map q.pr = (mt V g).map q.pr ∧
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram q.v (g * c⁻¹) = 1 := by
  obtain ⟨ε, hε, hE⟩ := q.above
  have hεε : ε * ε = ε := by rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε, GlobalTheory.SplitCut.eFin_idem]
  have hEE : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by rw [hE, ← map_mul, hεε]
  have hEc : cA D (q.e + cA D q.e) = q.e + cA D q.e := by rw [hE, GlobalTheory.SplitCut.cA_algebraMap]
  have h1 : GlobalTheory.FinPl.compAt D q.v (q.e + cA D q.e) = 1 := by
    obtain ⟨α, rfl, a1, -⟩ := hε
    rw [hE]
    change evalV D.host.F q.v α ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [a1]
    rfl
  obtain ⟨c, hc⟩ := GlobalTheory.SplitCut.cut_exists V g _ hEE hEc
  refine ⟨c, fun i j => ?_, ?_, ?_⟩
  · rw [hc]
    exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ hEE _ i j
  · rw [hc, GlobalTheory.GfCut.map_idem, GlobalTheory.LevelCut.pr_sum, one_smul, sub_self, zero_smul, add_zero]
  · rw [GlobalTheory.FinPl.KOpen.proj_eq_one_iff, ← GlobalTheory.FinPl.KOpen.map_eq_one_iff, GlobalTheory.SplitCut.mt_mul, Matrix.map_mul]
    have h2 : (mt V g).map (GlobalTheory.FinPl.compAt D q.v) = (mt V c).map (GlobalTheory.FinPl.compAt D q.v) := by
      rw [hc, GlobalTheory.GfCut.map_idem, h1, one_smul, sub_self, zero_smul, add_zero]
    rw [h2, ← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, mul_inv_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem moves_of_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    {h : GA D V} (hh : finE V h ∈ St β) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves V h Λ Λ P :=
  GlobalTheory.FinPl.KOpen.moves_of_levelOpen V Λ hΛ P (GlobalTheory.AdelicU.mem_levelOpen.2
    ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ h).1 hh))

theorem mem_levG_of_inK {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P (PP.under (𝓞 D.host.F))) {κ : GA D V} (hκ : GlobalTheory.FinPl.InK V Λ P κ) :
    κ ∈ levG V β L := by
  have hS : finE V κ ∈ St β := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ κ).2
    (GlobalTheory.AdelicU.mem_levelOpen.1 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK V Λ hΛ P hκ))
  obtain ⟨hf, h1⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V P κ).1 hκ.1
  exact ⟨hf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V κ) hS fun PP h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β κ PP hS (h1 _ (hP PP h))⟩

theorem mem_levG_iff_base {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr : r ≤ V.rank) (Pg Q Q₀ : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ₀ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (h₀ : Q₀ = ∅)
    (h : GA D V) : h ∈ levG V β (datY _ r t j hr Pg Q P χ ξ Frm.B) ↔ h ∈ levG V β (datY _ r t j hr Pg Q₀ P χ ξ₀ Frm.B) ∧
      ∀ PP ∈ Q, redFn β PP (finE V h) ∈ blockTri (blk2 r) := by
  subst h₀
  constructor
  · rintro ⟨hf, h1, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := mem_parLev.1 h1
    exact ⟨⟨hf, mem_parLev.2 ⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty _)⟩, h2⟩, a4⟩
  · rintro ⟨⟨hf, h1, h2⟩, a4⟩
    obtain ⟨a1, a2, a3, -⟩ := mem_parLev.1 h1
    exact ⟨hf, mem_parLev.2 ⟨a1, a2, a3, a4⟩, h2⟩

theorem red_iff_local {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : GlobalTheory.LocMod.Frame k V.rank Y)
    (J : Subgroup (GL Y k)) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {PP : Pl D.host.E} (hPP : PP ∈ L.Q) (hv : q.v = PP.under (𝓞 D.host.F))
    (hg : ∀ PP' ∈ L.Pg, PP'.under (𝓞 D.host.F) ≠ q.v) (hq : ∀ PP' ∈ L.Q, PP'.under (𝓞 D.host.F) = q.v → PP' = PP)
    {b : GA D V} (hb : b ∈ GfC V) (hm : GlobalTheory.FinPl.Moves V b Λ N (· = q.v)) (hN : IntIn q V Fr N)
    (hJ : ∀ x ∈ KO k Y, ∀ c, (ofSplit q).IsLoc Fr c x → (b⁻¹ * c * b ∈ levG V β L ↔ x ∈ J))
    {g : GA D V} (hS : finE V (b⁻¹ * g * b) ∈ St β) {x : GL Y k} (hx : (mt V g).map q.pr = Fr.β * x.val * Fr.γ) :
    redFn β PP (finE V (b⁻¹ * g * b)) ∈ blockTri (blk2 L.r) ↔ x ∈ J := by
  have hxK : x ∈ KO k Y := _root_.GlobalTheory.SplitInt.mem_KO_of_moves q V Fr N (· = q.v) rfl hN g
    ((GlobalTheory.StMoves.moves_conj_iff g hm).1 (moves_of_St hβ hΛ hS _)) x hx
  obtain ⟨c, c1, c2, c3⟩ := local_part q V g
  rw [← hJ x hxK c ⟨c1, c2.trans hx⟩]
  obtain ⟨cf, c4⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ c).1
    (GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D k q V c c1 (· = q.v) rfl)
  have p1 : ∀ u, u ≠ q.v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (b⁻¹ * c * b) = 1 := fun u hu => by
    rw [map_mul, map_mul, c4 u hu, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have p2 : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram q.v (b⁻¹ * (g * c⁻¹) * b) = 1 := by
    rw [map_mul, map_mul, c3, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have e : b⁻¹ * g * b = (b⁻¹ * (g * c⁻¹) * b) * (b⁻¹ * c * b) := by group
  have hSc : finE V (b⁻¹ * c * b) ∈ St β := by
    refine (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ _).2 fun u => ?_
    by_cases hu : u = q.v
    · have := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ _).1 hS u
      rw [e, map_mul, hu, p2, one_mul] at this
      rw [hu]
      exact this
    · rw [p1 u hu]
      exact one_mem _
  have hSd : finE V (b⁻¹ * (g * c⁻¹) * b) ∈ St β := by
    have := mul_mem hS (inv_mem hSc)
    rw [e, map_mul, mul_inv_cancel_right] at this
    exact this
  have r1 : redFn β PP (finE V (b⁻¹ * g * b)) = redFn β PP (finE V (b⁻¹ * c * b)) := by
    rw [e, map_mul, redFn_mul hSd hSc, GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSd (hv ▸ p2), one_mul]
  have r2 : ∀ PP' : Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ q.v → redFn β PP' (finE V (b⁻¹ * c * b)) = 1 := fun PP' h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP' hSc (p1 _ h)
  rw [r1]
  refine ⟨fun h => ⟨(GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hb) cf) hb, mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSc, fun PP' h' => ?_,
    fun PP' h' => ?_⟩, ?_⟩, fun h => parLev_q h.2.1 hPP⟩
  · rw [r2 PP' (hg PP' h')]
    exact one_mem _
  · by_cases h'' : PP'.under (𝓞 D.host.F) = q.v
    · rw [hq PP' h' h'']
      exact h
    · rw [r2 PP' h'']
      exact one_mem _
  · have : rTup β L (finE V (b⁻¹ * c * b)) = 1 := by
      funext PP'
      show upperLeftBlock L.hr (redFn β PP'.1 _) = 1
      rw [r2 PP'.1 (hg _ PP'.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [this]
    exact one_mem _

def moved {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) : Subgroup (GA D V) := K.comap (MulAut.conj b⁻¹).toMonoidHom

theorem mem_moved {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) (g : GA D V) : g ∈ moved b K ↔ b⁻¹ * g * b ∈ K := by
  simp [moved]

theorem moved_set {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) :
    {g : GfC V | b * g.1 * b⁻¹ ∈ moved b K} = {k : GfC V | k.1 ∈ (K : Set (GA D V))} := by
  ext g
  simp [mem_moved, mul_assoc]

theorem moved_level {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P (PP.under (𝓞 D.host.F))) {b : GA D V} (hb : b ∈ GfC V)
    (hm : GlobalTheory.FinPl.Moves V b Λ N P) :
    moved b (levG V β L) ≤ GfC V ∧ IsCompact (moved b (levG V β L) : Set (GA D V)) ∧
      IsOpen (((moved b (levG V β L)).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) ∧
      (∀ κ, GlobalTheory.FinPl.InK V N P κ → κ ∈ moved b (levG V β L)) ∧ ∀ g ∈ moved b (levG V β L), GlobalTheory.FinPl.Moves V g N N P := by
  refine ⟨fun g hg => ?_, ?_, ?_, fun κ hκ => ?_, fun g hg => ?_⟩
  · have h1 : b⁻¹ * g * b ∈ GfC V := ((mem_moved _ _ g).1 hg).1
    have e : g = b * (b⁻¹ * g * b) * b⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hb h1) (inv_mem hb)
  · have e : (moved b (levG V β L) : Set (GA D V)) = (fun x => b * x * b⁻¹) '' (levG V β L : Set (GA D V)) := by
      ext g
      constructor
      · intro hg
        exact ⟨b⁻¹ * g * b, (mem_moved _ _ g).1 hg, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (mem_moved _ _ _).2 ?_
        have e2 : b⁻¹ * (b * k * b⁻¹) * b = k := by group
        rw [e2]
        exact hk
    rw [e]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG V β L).image (by fun_prop)
  · have e : (((moved b (levG V β L)).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) =
        (fun x : GfC V => (⟨b, hb⟩ : GfC V)⁻¹ * x * ⟨b, hb⟩) ⁻¹' {g : GfC V | (g : GA D V) ∈ levG V β L} := by
      ext x
      exact mem_moved b (levG V β L) x.1
    rw [e]
    exact (GlobalTheory.LevelOpen.isOpen_levG V β L).preimage (by fun_prop)
  · have hn : (GlobalTheory.FinPl.grpAt V P).Normal := MonoidHom.normal_ker _
    refine (mem_moved _ _ κ).2 (mem_levG_of_inK hβ hΛ L hP ⟨?_, (GlobalTheory.StMoves.moves_conj_iff κ hm).2 hκ.2⟩)
    have := hn.conj_mem κ hκ.1 b⁻¹
    rwa [inv_inv] at this
  · exact (GlobalTheory.StMoves.moves_conj_iff g hm).1
      (moves_of_St hβ hΛ (parLev_St (lev_le_parLev ((mem_moved _ _ g).1 hg).2)) P)

theorem exists_mat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    ∃ x : GL Y k, (mt V g).map q.pr = Fr.β * x.val * Fr.γ := by
  have hm : ∀ a a' : GA D V, a * a' = 1 → (mt V a).map q.pr * (mt V a').map q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  exact GlobalTheory.LevelCut.exists_coord Fr _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))

theorem under_ne {T : Type} {L : LevCh D T} {t₀ : T} (h : L.Is t₀) (t : T) {PP PP' : Pl D.host.E} (hQ : PP ∈ L.Q t) (hg : PP' ∈ L.Pg) :
    PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) := by
  intro e
  obtain ⟨p, hp, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hQ
  obtain ⟨k, hk⟩ := (h.Pg PP').1 hg
  have key : ∀ (R : Pl D.host.E) (n : ℕ), (n : 𝓞 D.host.E) ∈ R.asIdeal ↔ (n : 𝓞 D.host.F) ∈ (R.under (𝓞 D.host.F)).asIdeal :=
    fun R n => by
      show _ ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) n ∈ R.asIdeal
      rw [map_natCast]
  exact GlobalTheory.LevelRamif.not_two_primes PP' hp (D.host.g_prime k) (hne k) ((key _ _).2 (e ▸ (key _ _).1 hm))
    (GlobalTheory.LevelRamif.typePrime_mem hk)

theorem base_empty {T : Type} {L : LevCh D T} {t₀ : T} (h : L.Is t₀) : L.Q t₀ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hP => (h.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [h.xi_base]
  rfl

end GlobalTheory.StepConst

end
