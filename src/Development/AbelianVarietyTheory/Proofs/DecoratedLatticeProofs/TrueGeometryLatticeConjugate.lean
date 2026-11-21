import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd.Bwd

section Dense
open Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.RootEx GlobalTheory.TwBridge ValuativeRel

theorem prX_le_of_prCat (X : Formalism.L2.Col.Fields) (Pr : Formalism.L2.Col.Primes X) (R : Ranks) (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (cst : Formalism.L2.Col.LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (K : Subgroup (GL (XIx (Fin R.k) (Fin R.t) j) k))
    (hKo : IsOpen (K : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)))
    (hle : ∀ e' : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' →
      ∀ y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ, GlobalTheory.VolBridge.locHom ι e' y ∈ K) :
    GlobalTheory.StepData.prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) ≤ K := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  have hord : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (GlobalTheory.VolBridge.eX e hcc heR) := fun a => he (Sum.inl a)
  set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
  set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g) :=
    GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
  have hpo : IsOpen (GlobalTheory.StepData.prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
    GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
  intro z hz
  have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k |
      v⁻¹ * z ∈ ((GlobalTheory.StepData.prX (Cgrp J g) ⊓ K : Subgroup _) : Set _)} :=
    (hpo.inter hKo).preimage (by fun_prop)
  obtain ⟨y, hy⟩ := GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem, hz])
  have hy1 : (φ' y)⁻¹ * z ∈ GlobalTheory.StepData.prX (Cgrp J g) := hy.1
  have hy2 : (φ' y)⁻¹ * z ∈ K := hy.2
  have hyC : φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g) := by
    have := mul_mem hz (inv_mem hy1); simpa using this
  have hyK : φ' y ∈ K := hle e' hord y ((hP y).2 hyC)
  have := mul_mem hyK hy2; simpa using this

end Dense

theorem adAt_eq_of_pr {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (z : Formalism.L2.Theta.AE D) (x : D.host.E) (h : q.pr z = q.pr (incA D x)) :
    adAt D.host.F PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x := by
  have h1 : q.e * z = q.e * incA D x := by rw [← q.sec_pr, ← q.sec_pr, h]
  have h2 := congrArg (fun w => GlobalTheory.StdFrames.cpt PP (toEAf D w)) h1
  simp only [RingHom.map_mul, (GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul] at h2
  rw [← GlobalTheory.SplitProj.cpt_eq_adAt, h2]
  exact (GlobalTheory.SplitProj.cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)

section Rat
open Formalism.L2.Col Formalism.UG
attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000 in

theorem mem_lev_of_rat {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is) (j : ℕ) (hj : j + 2 ≤ B.R.m) (β : Ch j)
    (hβ : A.kb j β = TC.kStd X u (B.R.N j)) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs)
    (x : TC.GA B (B.R.N j)) (hx : x ∈ UAd B.sp.cm (B.R.N j))
    (hoff : ∀ v', v' ≠ P.1.under (𝓞 B.host.F) → bc (prV (E := B.host.E) v') x = 1)
    (g : Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N j))
    (hg : g ∈ prCat (Pr := B.primes X) (I.cst a).sharp j P.1 ((I.idx a).h j ((A.b0 j β).get (by omega)) P))
    (hpt : ∀ r s, adAt B.host.F P.1 (x.1 r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) (g (Pi.single s 1) r)) :
    x ∈ (A.K j (by omega) β).lev.U := by
  have hj' : j ≤ B.R.m := by omega
  have hjm : j < B.R.m := by omega
  have hL := hI.idx_ok a
  have hR := hA.reads j hj'
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hj' β
  have hc := (hA.rep j hj' c).1
  rw [← hc] at hg
  have hPQ : P.1 ∈ I.Q a := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
  obtain ⟨hLev, hdisj, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) hdisj
  have hp := IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (A.chOf j c)
  have hv : Formalism.L2.Col.IsOver (P.1.under (𝓞 B.host.F)) P.1 := rfl
  have hgI : g ∈ GLint B.fields.E (B.R.N j) P.1 := hL.int j _ P hg
  have hT := (GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad I hI l u a (P.1.under (𝓞 B.host.F)) ⟨P.1, hPQ, rfl⟩).1
  have hk1 : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb j (A.chOf j c)) = 1 := by
    rw [hβ]; exact (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) l.pr u (B.R.N j)).2.1 _ hT
  let cc : GLQ B.fields.E (B.R.N j) (I.Q a) := Pi.mulSingle (⟨P.1, hPQ⟩ : I.Q a) (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1)
  have hccP : cc ⟨P.1, hPQ⟩ = (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1) := Pi.mulSingle_eq_same _ _
  have hccO : ∀ P'' : I.Q a, P''.1 ≠ P.1 → cc P'' = 1 := fun P'' h => Pi.mulSingle_eq_of_ne (fun e => h (congrArg Subtype.val e)) _
  have hb : c.1 = Idx.of (c.1.get hjm) hjm := (Idx.of_get c.1 hjm _).symm
  have hcc : cc ∈ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp := by
    rw [hb]
    intro P'' _
    by_cases h : P''.1 = P.1
    · obtain rfl : P'' = ⟨P.1, hPQ⟩ := Subtype.ext h
      show cc ⟨P.1, hPQ⟩ ∈ ((I.idx a).levQ j (c.1.get hjm) ⟨P.1, hPQ⟩).H
      rw [hccP, hL.grpQ]
      exact inv_mem (Subgroup.mem_subgroupOf.2 hg)
    · show cc P'' ∈ ((I.idx a).levQ j (c.1.get hjm) P'').H
      rw [hccO P'' h]
      exact one_mem _
  let κ : (I.stp u a j).G c.1 := (1, 1, ⟨cc, hcc⟩)
  have hPu : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    simp only [uSG, Finset.mem_union]
    exact Or.inr (ColIn.Q_subset_SQ I a hPQ)
  have key := GlobalTheory.Mem.Col2.LevLiftPt.core B.sp.cm hp hx hpk.uni _ P.1 hv hoff g hgI (fun r s => by
      have e : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) ((A.kb j (A.chOf j c))⁻¹ * x * A.kb j (A.chOf j c)) =
          bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) x := by
        rw [map_mul, map_mul, map_inv, hk1, inv_one, one_mul, mul_one]
      exact (GlobalTheory.Mem.Col2.ChTwRead.adAt_congr_prV P.1 (congrArg (fun m => m.1 r s) e)).trans (hpt r s))
    (GlobalTheory.Mem.Col2.LevLiftPt.vT_notOver I hI a P _ hv u) (fun w hw hwv => by
      have hw' : w ∈ uSG (B.primes X).vGs I.SQ := by
        simp only [uSG, Finset.mem_union]
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr (ColIn.Q_subset_SQ I a h)
      rcases rll_over_cases B.sp.cm hv hwv with h | h
      · exact h
      · exact absurd (h ▸ hw') (hLev.split P.1 hPu))
    1 cc (fun h => absurd h hP) (fun w _ y _ => by simp) (fun _ => by rw [hccP, inv_inv])
    (fun P'' h => by rw [hccO P'' h, inv_one]; rfl)
  have e := GlobalTheory.Mem.Col2.LevLiftPt.mul_conj (G := TC.GA B (B.R.N j)) ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1 x (A.kb j (A.chOf j c))
  have hq : TC.PtOf ((show TC.GA B (B.R.N j) from ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1) * x * A.kb j (A.chOf j c))
      ((I.stp u a j).act c.1 κ ((I.stp u a j).rep c)).1.1 := e ▸ key
  refine (hR.lev c x _ hq).2 ⟨κ, map_one (ufGL B.fields.E (B.R.N j)), rfl, ?_⟩
  have h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, p.1.2 = ∅ := fun p => by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by omega)] at this
    exact this
  funext P'
  simp only [cosetIn, h0, Set.mem_empty_iff_false, false_and, exists_false]

end Rat

theorem entry_of_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y) (e : Y ≃ Fin N)
    (he : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e) (M : Matrix (Fin N) (Fin N) k) (g : Matrix Y Y k)
    (h : M = F.β * g * F.γ) (a b : Y) : M (e a) (e b) = g a b := by
  have h1 : M * F.β = F.β * g := by rw [h, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [he] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2

open GlobalTheory.FinPl in

theorem grpAt_empty {D : D7} (V : HSp D) {P : Pl D → Prop} (hP : ∀ w, ¬ P w) (n : GA D V) (hn : n ∈ grpAt V P) : n = 1 := by
  rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at hn
  apply GlobalTheory.FinPlLoc.mt_inj
  rw [GlobalTheory.FinPlLoc.mt_one]
  ext i j
  have := GlobalTheory.FinPlLoc.eq_zero_of_comp _ (hn i j).1 (fun w => (hn i j).2 w (hP w))
  rw [Matrix.sub_apply, sub_eq_zero] at this
  exact this

open GlobalTheory.FinPl in

theorem locHom_one_of_off {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {x : GA D S} (h1 : x ∈ grpOff S (· = q.v)) : GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

open GlobalTheory.FinPl in

theorem grpAt_le_of {D : D7} (V : HSp D) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) {n : GA D V} (hn : n ∈ grpAt V P) :
    n ∈ grpAt V P' := by
  rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at hn ⊢
  exact fun i j => ⟨(hn i j).1, fun w hw => (hn i j).2 w (fun hp => hw (h w hp))⟩

end GlobalTheory.LevProd.Bwd
end
