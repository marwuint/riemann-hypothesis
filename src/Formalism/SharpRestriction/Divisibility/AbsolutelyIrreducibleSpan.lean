import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HermitianLattices.StatementMaj
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace Formalism.MainNotions.AbsolutelyIrreducibleSpan

open Formalism.BasicNotions

section LLStr

variable {LL : Type} [Field LL] (φ : LL →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]

def llSpan (S : Set W) : Set W :=
  {x | ∃ (s : Finset W) (c : W → LL), (↑s : Set W) ⊆ S ∧ x = ∑ v ∈ s, φ (c v) • v}

end LLStr

structure Lev (D : D7) where
  EE : Type
  [nEE : NormedAddCommGroup EE]
  [iEE : InnerProductSpace ℂ EE]
  [fEE : FiniteDimensional ℂ EE]
  S : RowSide D EE
  n : ℕ
  onb : OrthonormalBasis (Fin n) ℂ EE
  ft : Fin n → D.what₂.FT

attribute [instance] Lev.nEE Lev.iEE Lev.fEE

def Lev.of {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) : Lev D :=
  { EE := EE, S := S, n := n, onb := b, ft := ty }

def Lev.sharp (D : D7) : Lev D := Lev.of (RowSide.sharp D) D.what₂.onb D.what₂.ft

def Lev.p0 {D : D7} (P : BaseLevelRowSide D) : Lev D := Lev.of P.s D.what₂.onb0 D.what₂.ft0

def Lev.kap {D : D7} (V : Lev D) : ℝ := V.S.kapOf V.ft

theorem sharp_downTo (D : D7) (μ : D.what₂.Tup) :
    ∀ j, (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j
  | 0 => rfl
  | j + 1 => by
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [sharp_downTo D μ j]; rfl

theorem sharp_iota (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  first
  | (unfold RowSide.iota Rows.Data.iota; rw [sharp_downTo D μ D.R.m]; try rfl; done)
  | (simp only [RowSide.iota, Rows.Data.iota, sharp_downTo]; try rfl; done)
  | rfl

theorem sharp_Usp (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).Usp μ = D.what₂.Usp μ := by
  first
  | (unfold RowSide.Usp Rows.Data.Usp; rw [sharp_iota]; try rfl; done)
  | (simp only [RowSide.Usp, Rows.Data.Usp, sharp_iota]; try rfl; done)
  | rfl

theorem sharp_Qsp (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).Qsp μ = D.what₂.Qsp μ := by
  first
  | (unfold RowSide.Qsp Rows.Data.Qsp; rw [sharp_Usp]; try rfl; done)
  | (simp only [RowSide.Qsp, Rows.Data.Qsp, sharp_Usp]; try rfl; done)
  | rfl

theorem sharp_LamSet (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).LamSet μ = D.what₂.LamSet μ := by
  first
  | (unfold RowSide.LamSet Rows.Data.LamSet; rw [sharp_Qsp]; try rfl; done)
  | (simp only [RowSide.LamSet, Rows.Data.LamSet, sharp_Qsp]; try rfl; done)
  | rfl

theorem sharp_RRset (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).RRset μ = D.what₂.RRset μ := by
  first
  | (unfold RowSide.RRset Rows.Data.RRset; rw [sharp_iota, sharp_LamSet]; try rfl; done)
  | (simp only [RowSide.RRset, Rows.Data.RRset, sharp_iota, sharp_LamSet]; try rfl; done)
  | rfl

theorem sharp_RRDef (D : D7) : (RowSide.sharp D).RRDef ↔ DV.RRDef D := by
  first
  | (unfold RowSide.RRDef DV.RRDef; simp only [sharp_RRset]; try exact Iff.rfl; done)
  | exact Iff.rfl

section Derived

variable (D : D7)

def v0 : InfinitePlace D.what₂.LL := InfinitePlace.mk D.what₂.embLL

def rPr : ℕ :=
  sInf {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}

def q0 : ℕ := sInf {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}

theorem condE_pos : 0 < LevelStarExponents.condE D := by
  unfold LevelStarExponents.condE
  exact Nat.mul_pos (Nat.mul_pos D.host.QS_pos (lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.1))
    (lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2)

theorem absNorm_ccK_pos : 0 < Ideal.absNorm D.host.ccK := by
  first
  | exact Nat.pos_of_ne_zero (fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  | (rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot)

theorem rPr_mem : (rPr D).Prime ∧
    ¬ rPr D ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK := by
  have hN : 0 < LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK := by
    have h1 := D.host.pde_prime.two_le
    have h2 := D.host.pde'_prime.two_le
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (condE_pos D) (by omega)) (by omega)) (absNorm_ccK_pos D)
  obtain ⟨p, hp1, hp2⟩ :=
    Nat.exists_infinite_primes (LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK + 1)
  have hne : {p : ℕ | p.Prime ∧
      ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}.Nonempty :=
    ⟨p, hp2, fun hd => absurd (Nat.le_of_dvd hN hd) (Nat.not_le.mpr (Nat.lt_of_succ_le hp1))⟩
  exact Nat.sInf_mem hne

theorem auxiliary_prime_mem : (q0 D).Prime ∧ q0 D % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ q0 D ∣ Ideal.absNorm D.host.ccK := by
  have hr := (rPr_mem D).1
  have hc := condE_pos D
  have hk : 1 < rPr D * LevelStarExponents.condE D :=
    lt_of_lt_of_le hr.one_lt (le_mul_of_one_le_right (Nat.zero_le _) hc)
  obtain ⟨p, hp, hlt, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (Ideal.absNorm D.host.ccK) (Nat.pos_iff_ne_zero.mp (lt_trans Nat.zero_lt_one hk))
  have hne : {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}.Nonempty :=
    ⟨p, hp, (show p % _ = 1 % _ from hmod).trans (Nat.mod_eq_of_lt hk),
      fun hd => absurd (Nat.le_of_dvd (absNorm_ccK_pos D) hd) (Nat.not_le.mpr hlt)⟩
  exact Nat.sInf_mem hne

end Derived

def hBot : ℕ → ℕ := fun _ => 0

def hTop (m : ℕ) : ℕ → ℕ := fun i => if i < m then m else 0

def flipP (h : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := Function.update h i (h i + 1)

open Formalism.BasicNotions.TH (Ix Mat ProvA)

structure ThetaTh where
  Sp : Type
  rk : Sp → ℕ
  witt : Sp → ℕ
  AF : Sp → Type
  [aAF : ∀ V, AddCommGroup (AF V)]
  [mAF : ∀ V, Module ℂ (AF V)]
  cusp : ∀ V, Submodule ℂ (AF V)
  pet : ∀ V, AF V → AF V → ℂ
  Dat : Sp → Sp → Type
  lift : ∀ W V, Dat W V → AF W →ₗ[ℂ] AF V
  Tst : Sp → ℕ → Bool → Type
  per : ∀ V c b, Tst V c b → AF V →ₗ[ℂ] ℂ
  tcusp : ∀ V c b, Tst V c b → Prop
  tpure : ∀ V c b, Tst V c b → Prop
  taniso : ∀ V c b, Tst V c b → Prop
  tmatch : ∀ W V c b, Dat W V → Tst V c b → Prop
  Hq : ∀ (_W V : Sp) (c : ℕ) (b : Bool), Tst V (c + 1) b → Type
  itInt : ∀ W V c b (ph : Tst V (c + 1) b), (Hq W V c b ph → ℂ) → ℂ
  tlift : ∀ W V c b, Dat W V → ∀ ph : Tst V (c + 1) b, Hq W V c b ph → Tst W c (!b)
  tl0 : ∀ W V b, Dat W V → Tst V 0 b → AF W
  tl0cusp : ∀ W V b, Dat W V → Tst V 0 b → Prop
  PlS : Type
  fac : ∀ W V, PlS → Dat W V → Dat W V → AF W → AF W → Prop
  lowerZero : ∀ W V, Dat W V → AF W → Prop
  LS : ∀ W V, PlS → Dat W V → AF W → ℝ → ℂ
  dS : ∀ W V, PlS → Dat W V → ℂ
  Zloc : ∀ W V, PlS → Dat W V → Dat W V → AF W → AF W → ℂ
  cR : Sp → Sp → ℂ
  embC : ∀ W, AF W → AF W → ℂ

attribute [instance] ThetaTh.aAF ThetaTh.mAF

structure LocV (D : D7) (V : Lev D) (A : AmbForm D V.S) where
  kapV : InfinitePlace D.what₂.LL → ℝ
  kapV_pos : ∀ v, 0 < kapV v
  kapV_base : kapV (v0 D) = V.kap
  plS : Finset D.what₂.places.Pl
  plS_mu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ plS
  s : ℕ
  s_odd : Odd s
  s_lo : D.R.r + 5 < s
  s_hi : s ≤ D.R.r + 7
  cInf : ℕ → D.what₂.Tau → ℚ
  chi_above : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ (j : Fin D.R.m) τ,
    2 * ((D.R.k + D.R.m * (D.R.t + s + 1) : ℕ) : ℚ) ^ 3 < 2 * ((D.hc τ).e j + cInf i τ)
  ev0 : ℕ
  nb : Fin D.R.m → ℚ
  ar : ProvA
  th : ThetaTh
  vx : ℕ → ℕ → th.Sp
  vx_rk : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → th.rk (vx i j) = D.R.r + j * D.R.t + i * s
  vx_witt : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → th.witt (vx i j) ≤ (D.R.m - j) / 2
  Pp : ℕ → th.Sp
  Pp_rk : ∀ i, i ≤ D.R.m → th.rk (Pp i) = D.R.r + 1 + i * (s - 1)
  Pp_witt : ∀ i, i ≤ D.R.m → th.witt (Pp i) ≤ (D.R.m - i + 1) / 2
  real : V.EE →ₗ[ℂ] th.AF (vx 0 0)
  real_inj : Function.Injective real
  real_cusp : ∀ u, real u ∈ th.cusp (vx 0 0)
  MM : HLat D.what₂.LL
  MM_good : MM.Good
  DatX : Type
  [finDat : Fintype DatX]
  I0 : Type
  mmIx : MM.ι ≃ DatX × I0
  tst : I0 → th.Tst (vx D.R.m 0) (D.R.m - 1) true
  datRow : DatX → ∀ i, th.Dat (vx i 0) (vx (i + 1) 0)
  PD : D.what₂.Tup → (ℕ → ℕ) → Type
  [aPD : ∀ μ h, AddCommGroup (PD μ h)]
  [mPD : ∀ μ h, Module ℂ (PD μ h)]
  ev : ∀ μ h, PD μ h →ₗ[ℂ] V.S.Amb μ →ₗ[ℂ] th.AF (vx D.R.m 0)
  T0 : ∀ μ, DatX → PD μ hBot
  Good : ∀ μ h, Set (PD μ h)
  IntAt : ∀ μ h, D.what₂.places.Pl → ℝ → Set (PD μ h)
  SzAt : ∀ μ h, InfinitePlace D.what₂.LL → ℝ → Set (PD μ h)
  Rep : D.what₂.Tup → (ℕ → ℕ) → ℕ → Type
  pA : ∀ μ h i, PD μ (flipP h i) → Rep μ h i
  pB : ∀ μ h i, PD μ h → Rep μ h i
  csq : D.what₂.Tup → ℕ → ℕ → ℂ
  vT : ∀ μ, PD μ (hTop D.R.m) → I0 → Module.Dual D.what₂.LL (A.MtH μ).V
  App : ℂ
  KI : Type
  kS : KI → HLat D.what₂.LL
  kT : KI → HLat D.what₂.LL
  kmap : ∀ k, (kS k).V →ₗ[D.what₂.LL] (kT k).V
  kTup : KI → D.what₂.Tup
  kdeg : KI → ℕ
  kdepth : KI → ℕ → ℕ
  U1 : Submodule ℂ (th.AF (vx 0 0))
  MS : ℕ → Type
  [aMS : ∀ i, AddCommGroup (MS i)]
  [mMS : ∀ i, Module ℂ (MS i)]
  DatP : ℕ → Type
  Dn : ∀ i, DatP i → MS (i + 1) →ₗ[ℂ] MS i
  Up : ∀ i, DatP i → MS i →ₗ[ℂ] MS (i + 1)
  phi0 : ∀ i, DatP i
  DatS : Type
  cmb : DatS → DatX → ℂ
  datPof : DatS → ∀ i, DatP i
  Phi0 : DatS
  phi_data_at_base : datPof Phi0 = phi0
  psiMS : I0 → MS D.R.m
  psi_span : Submodule.span ℂ (Set.range psiMS) = ⊤
  lamPer : MS 0 →ₗ[ℂ] th.AF (vx 0 0) →ₗ[ℂ] ℂ
  Irr : Set (MS 0)
  Ap : ℂ
  volS : ℝ
  volS_pos : 0 < volS
  cRal : ℕ → ℂ
  LSpi : MS 0 → ℕ → ℂ
  Lchi : ℕ → ℕ → ℕ → ℂ
  dSv : ℕ → ℂ
  ZS : ℕ → ℝ

attribute [instance] LocV.finDat LocV.aPD LocV.mPD LocV.aMS LocV.mMS

theorem auxiliary_prime_odd (D : D7) : q0 D % 2 = 1 := by
  have h2 : 2 ∣ D.host.QS := by
    have ht := D.host.tower_dvd
    exact dvd_trans (dvd_pow_self 2 (by omega)) ht
  have h2c : 2 ∣ LevelStarExponents.condE D := by
    unfold LevelStarExponents.condE
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _
  have h2k : 2 ∣ rPr D * LevelStarExponents.condE D := dvd_mul_of_dvd_right h2c _
  rw [← Nat.mod_mod_of_dvd (q0 D) h2k, (auxiliary_prime_mem D).2.1]
  all_goals norm_num

structure Consts where
  Cf : ℝ
  Cp : ℝ
  CPP : ℝ
  Cint : ℝ
  Clin : ℝ
  Ctr : ℝ
  Cten : ℝ
  Cgr : ℝ
  Cval : ℝ
  Cfp : ℝ
  Cfp' : ℝ
  Cip : ℝ
  Cmm : ℝ

section Stmt

variable (D : D7) {V : Lev D} {A : AmbForm D V.S}

def RRDef (_X : LocV D V A) : Prop :=
  Set.range V.S.jEE = llSpan D.what₂.embLL (V.S.RRset D.what₂.mu0) ∧ V.S.RRDef

end Stmt

end Formalism.MainNotions.AbsolutelyIrreducibleSpan
