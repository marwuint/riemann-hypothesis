import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm

noncomputable section
namespace GlobalTheory.LevProd.Fwd

section Columns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Col2.PtExist
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem ratM_inj {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) {f g : Sp E n ≃ₗ[E] Sp E n}
    (h : ratM P f = ratM P g) : f = g := by
  refine LinearEquiv.ext fun x => funext fun i => (algebraMap E (P.adicCompletion E)).injective ?_
  have h1 := congrFun (ratM_mulVec (P := P) f x) i
  have h2 := congrFun (ratM_mulVec (P := P) g x) i
  rw [← h1, ← h2, h]

theorem exists_gl_mat {E : Type} [Field E] [NumberField E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) : ∃ γ : GL (Fin n) E, γ.1 = mat f := by
  have h1 : mat (1 : Sp E n ≃ₗ[E] Sp E n) = 1 := by
    ext i j
    show (Pi.single j 1 : Sp E n) i = _
    rw [Matrix.one_apply, Pi.single_apply]
  exact ⟨⟨mat f, mat f⁻¹, by rw [← mat_mul, mul_inv_cancel, h1], by rw [← mat_mul, inv_mul_cancel, h1]⟩, rfl⟩

theorem mem_levQ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (hx : x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i)) (hxU : x ∈ U (chOf c))
    (hk1 : ∀ P : I.Q a, locM P.1 (k (chOf c)) = 1)
    (γ : I.Q a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)))
    (hγ : ∀ P : I.Q a, locM P.1 x = ratM P.1 (γ P)) (P : I.Q a) :
    ∃ κ ∈ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1 P).H, κ.1 = γ P := by
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hy : ∀ P : I.Q a, locM P.1 (y c * x * k (chOf c)) = ratM P.1 (((I.stp u a i).rep c).1.1.fr P * γ P) := by
    intro P
    have h1 : locM P.1 (y c * k (chOf c)) = ratM P.1 (((I.stp u a i).rep c).1.1.fr P) := Matrix.ext fun r s => hp.fr P r s
    rw [locM_mul, hk1, Matrix.mul_one] at h1
    rw [locM_mul, locM_mul, hk1, Matrix.mul_one, ratM_mul, h1, hγ]
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat B.sp.cm ((B.primes X).vT u) (B.primes X).vGs (I.Q a) _ hg' fun P hP => by
    obtain ⟨δ, hδ⟩ := exists_gl_mat (((I.stp u a i).rep c).1.1.fr ⟨P, hP⟩ * γ ⟨P, hP⟩)
    refine ⟨δ, fun r s => ?_⟩
    rw [hδ]
    exact congrFun (congrFun (hy ⟨P, hP⟩) r) s
  obtain ⟨κ, hκ1, hκq, -⟩ := (hR.lev c x q hq).1 hxU
  have hκ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  have h2 : locM P.1 (y c * x * k (chOf c)) = ratM P.1 (q.fr P) := Matrix.ext fun r s => hq.fr P r s
  have h3 : q.fr P = κ.1.1 * ((I.stp u a i).rep c).1.1.fr P * ((κ.2.2.1 P)⁻¹).1 := by
    rw [← hκq]
    rfl
  rw [hy, h3, hκ] at h2
  have h4 := ratM_inj P.1 h2
  refine ⟨(κ.2.2.1 P)⁻¹, inv_mem (κ.2.2.2 P (Set.mem_univ _)), ?_⟩
  have h5 : ((1 : UF B.fields.E (B.R.N i)).1 : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) = 1 := rfl
  rw [h5, one_mul] at h4
  exact (mul_left_cancel h4).symm

end Columns

section Local
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem prCat_iff (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (e₀ : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j)) (he₀ : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e₀) :
    IsOpen (prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) ∧
    ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ GlobalTheory.VolBridge.locHom ι e₀ y ∈ prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) := by
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
  have hee : e₀ = GlobalTheory.VolBridge.eX e hcc heR := Equiv.ext fun a => Fin.ext ((he₀ a).trans (he (Sum.inl a)).symm)
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  refine ⟨GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO), ?_⟩
  rw [hee]
  exact GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC

end Local

section Split
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.AdForm GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adAt_of_pr (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (z : AE D) (x : D.host.E) (h : q.pr z = q.pr (incA D x)) :
    adAt D.host.F PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x := by
  have h1 : q.e * z = q.e * incA D x := by rw [← q.sec_pr, ← q.sec_pr, h]
  have h2 := congrArg (fun w => adAt D.host.F PP (toEAf D w)) h1
  simp only [map_mul, GlobalTheory.AdForm.CongAtIdem.adAt_toEAf_of_isIdemAt he, one_mul] at h2
  exact h2.trans (adAt_inclE D.host.F PP x)

theorem locM_of_pr (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (x : GL (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)) (hx : x.1 = finM V hn g)
    (y : Formalism.L2.Col.Sp D.host.E n ≃ₗ[D.host.E] Formalism.L2.Col.Sp D.host.E n)
    (hy : ∀ r s, q.pr (mt V g (Fin.cast hn.symm r) (Fin.cast hn.symm s)) = q.pr (incA D (y (Pi.single s 1) r))) :
    GlobalTheory.Mem.ColAd.locM PP x = GlobalTheory.Mem.ColAd.ratM PP y :=
  Matrix.ext fun r s => (congrArg (adAt D.host.F PP) (congrFun (congrFun hx r) s)).trans (adAt_of_pr q PP he _ _ (hy r s))

theorem locHom_std (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (e : Y ≃ Fin S.rank) (hF : F.β = (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e) (g : GA D S) (r b : Y) :
    (GlobalTheory.LevIdx.locHom q S F g).val r b = q.pr (mt S g (e r) (e b)) := by
  have h := (GlobalTheory.LevIdx.eq_locHom_iff q S F g _).2 rfl
  have h2 := congrFun (congrFun h (e r)) (e b)
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std F e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std F e hF] at h2
  exact h2.symm

theorem locHom_eq_one {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {Y : Type} [Fintype Y] [DecidableEq Y] (q' : GlobalTheory.FinPl.SplitPt D k') (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : Frame k S.rank Y)
    (hv : q.v ≠ q'.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S (· = q'.v)) : GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff S (· = q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S (· = q'.v) (· = q.v) (fun p hp e => hv (e.symm.trans hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

end Split

theorem list_prod_map_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → ((l.map fun i => Pi.mulSingle i (x i) k).prod = if k ∈ l then x k else 1)
  | [], _ => by simp
  | b :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle x k l hl.2]
    by_cases hb : b = k
    · subst hb
      simp [hl.1]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hb), one_mul]
      simp [List.mem_cons, Ne.symm hb]

theorem list_prod_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) :
    ((List.finRange n).map fun i => Pi.mulSingle i (x i)).prod = x := by
  funext k
  rw [Pi.list_prod_apply, List.map_map]
  have := list_prod_map_mulSingle x k (List.finRange n) (List.nodup_finRange n)
  simpa [Function.comp_def] using this

end GlobalTheory.LevProd.Fwd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

namespace GlobalTheory.LevProd.Fwd

end GlobalTheory.LevProd.Fwd

namespace GlobalTheory.LevProd
end GlobalTheory.LevProd
end
