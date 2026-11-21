import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw

section Sign
variable {D : D7} {c : Comm D} {t : Tup c}

variable {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}

def QGeo.Res (G : QGeo v B PP) (δ : G.kˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ (z : 𝓞 D.host.E) (x : G.kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), (x : G.k) = (ofSplit G.q).pr (z : D.host.E) →
    (r : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ r)⁻¹

def QExt.tw {G : QGeo v B PP} {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) : GlobalTheory.TwBridge.TwData G.k :=
  ⟨G.ϖ, G.unif, G.ψk, hψ, G.cond, E.δ, E.tame, E.η, E.unr, sg⟩

structure QGeo.FrTie (G : QGeo v B PP) (fr : ∀ i, i ≤ D.R.m → Matrix (Fin (c.X i).rank) (Fin (D.R.N i)) D.host.E) : Prop where
  frX : ∀ i (hi : i ≤ G.s + 1) (hm : i ≤ D.R.m), ∃ e : XIx (Fin D.R.k) (Fin D.R.t) i ≃ Fin (D.R.N i),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e ∧ ∀ r a, (G.FX i hi).β r a = (ofSplit G.q).pr (fr i hm r (e a))
  frM : ∀ hm : G.s + 1 + 1 ≤ D.R.m, ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2) ⊕ Unit ≃ Fin (D.R.N (G.s + 1 + 1)),
    GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => D.R.N D.R.m - 1) e ∧
      ∀ r a, G.FM.β r a = (ofSplit G.q).pr (fr (G.s + 1 + 1) hm r (e a))

theorem exists_xOrd (R : Ranks) (j : ℕ) :
    ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := by
  have h : R.k + j + j * R.t = R.N j := by
    show _ = R.k + j * (R.t + 1)
    ring
  refine ⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr h), ?_⟩
  rintro ((i | i) | ⟨p, q⟩) <;> simp [GlobalTheory.SymBridge.xPos, finProdFinEquiv]
  ring

theorem exists_topOrd (R : Ranks) (s : ℕ) (hs : s + 1 + 1 = R.m) :
    ∃ e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N (s + 1 + 1)),
      GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => R.N R.m - 1) e := by
  have h : R.k + (s + 1) + (s + 2) * R.t + 1 = R.N (s + 1 + 1) := by
    show _ = R.k + (s + 1 + 1) * (R.t + 1)
    ring
  refine ⟨((Equiv.sumCongr ((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv)
    finOneEquiv.symm).trans finSumFinEquiv).trans (finCongr h), ?_⟩
  rintro (((i | i) | ⟨p, q⟩) | i)
  · simp [GlobalTheory.SymBridge.zPos]
  · simp [GlobalTheory.SymBridge.zPos]
  · simp [GlobalTheory.SymBridge.zPos, finProdFinEquiv]
    ring
  · simp [← hs, ← h]

end Sign

section True
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)

abbrev BadPr (I : TC B X) (a : I.ι) : Type := Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)

def locLast (I : TC B X) (a : I.ι) (P : BadPr I a) : ∀ (i : ℕ), i + 1 = B.R.m →
    Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → Formalism.L2.Col.Sp B.fields.E (B.R.N i) → B.fields.K
  | 0, h => absurd B.R.two_le_m (by omega)
  | n + 1, h => fun y y' => TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P (castSp B.fields.E (congrArg B.R.N h) ∘ₗ y) y'

def locXi (i : ℕ) (α : Ch₀ i) (γ : Ch₀ (i + 1)) (P : BadPr I a)
    (x : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) : B.fields.K :=
  let y := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (i + 1) γ).1.1 P) x
  if h : i + 2 < B.R.m then
    Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i ((A.b0 i α).get (by omega)) P)
      ((I.idx a).h (i + 1) ((A.b0 (i + 1) γ).get (by omega)) P) y
  else if h : i + 2 = B.R.m then
    Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i ((A.b0 i α).get (by omega)) P) y
      ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (i + 1) γ).1.1 P).symm (Formalism.L2.Col.repY (A.p0 (i + 1) γ).1.2))
  else if h : i + 1 = B.R.m then
    locLast I a P i h y ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i α).1.1 P).symm (Formalism.L2.Col.repY (A.p0 i α).1.2))
  else 0

abbrev homOf (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) :=
  toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z

def xiOff (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (Formalism.L2.Col.phiT B.fields.K (A.p0 i α).1.1.deco.1 (A.p0 (i + 1) γ).1.1.deco.1 (homOf I l Z i hi z) *
    ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∈ (B.primes X).vGs), locXi A i α γ P (homOf I l Z i hi z))

def BaseCommon : Prop := ∀ i, i ≤ B.R.m → ∀ β β', (A.p0 i β).1.1 = (A.p0 i β').1.1 ∧ A.kA i β = A.kA i β' ∧ A.xr i β = A.xr i β'

def baseFr (P : BadPr I a) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch₀ i) :
    Matrix (Fin ((I.rec7 l Z).sp.X i).rank) (Fin (B.R.N i)) (I.rec7 l Z).host.E := fun r b =>
  Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i β).1.1 P (Pi.single b 1) (finCongr (rankN (I.rec7 l Z) i hi) r)

variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle}

structure ReadsAt (P : BadPr I a) (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) (π : ∀ j, Ch₀ j → E.Ch j) : Prop where
  eq : P.1 = PP
  tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg)
  M : E.M = (I.cst a).M
  rep : ∀ j d (h : j + d = G.s) (hj : j < B.R.m) β, GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := G.k) (G.q.pr.comp (incA (I.rec7 l Z)))
    ((I.idx a).h j ((A.b0 j β).get hj) P) (E.rep j d h (π j β))

variable (G) in

def ownVec (P : BadPr I a) (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))) (β : Ch₀ (G.s + 1)) :
    XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) → G.k := fun r => (ofSplit G.q).pr
  ((Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (G.s + 1) β).1.1 P).symm (Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2) (e r))

structure MovedAt (P : BadPr I a) (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ) (π : ∀ j, Ch₀ j → E.Ch j) : Prop
    extends ReadsAt A P E hψ sg π where
  rk : ∀ i, (c.X i).rank = ((I.rec7 l Z).sp.X i).rank
  low : ∀ i (hi : i ≤ G.s) (hm : i ≤ B.R.m) β (e : XIx (Fin B.R.k) (Fin B.R.t) i ≃ Fin (B.R.N i)),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r b,
      (ofSplit G.q).pr (baseFr A P i hm β (Fin.cast (rk i) r) (e b)) = (G.FX i (Nat.le_succ_of_le hi)).β r b
  pen : ∀ (hm : G.s + 1 ≤ B.R.m) β (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∃ κ ∈ ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J,
      (∀ r b, (ofSplit G.q).pr (baseFr A P (G.s + 1) hm β (Fin.cast (rk _) r) (e b)) =
        ((G.FX (G.s + 1) le_rfl).β * κ.val.toBlocks₁₁) r b) ∧
      E.cos (π (G.s + 1) β) = Submodule.Quotient.mk (κ.val.toBlocks₁₁ *ᵥ ownVec A G P e β)

variable {A}

variable (A)

theorem ownVec_mem (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (hc : GlobalTheory.SymBridge.IsCompl (E := B.fields.E) P.1 (Formalism.L2.Col.qOf P.1) (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ) (e) (β) :
    ownVec A G P e β ∈ box _ (G.ϖ ^ (I.cst a).M)⁻¹ := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have h0 := (A.p0 (G.s + 1) β).repY_mem hs
  obtain ⟨y, hy, hY⟩ := (A.p0 (G.s + 1) β).mem_ybSet hs
  set z := Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2 with hz
  rw [hY] at h0
  have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy P
  have h2 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 h0 P
  simp only [if_neg hP] at h1 h2
  have hq : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := fun h => G.ϖ.ne_zero (by rw [hc.unif, h, map_zero])
  have h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.p0 (G.s + 1) β).1.1.deco.1.N := by
    have h4 := add_mem h1 (Submodule.smul_mem _ (((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) ^ (2 * (I.cst a).M)) h2)
    convert h4 using 1
    rw [← algebraMap_smul B.fields.E (((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) ^ (2 * (I.cst a).M)), smul_smul, map_pow, map_natCast,
      _root_.zpow_neg, inv_inv, zpow_natCast, two_mul, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one, ← smul_add, add_sub_cancel]
  rw [← (ptFr (A.p0 (G.s + 1) β).1.1 P.1).apply_symm_apply (_ • z)] at h3
  have h5 := (isFr_ptFr (A.p0 (G.s + 1) β).1.1 P.1 _).1 h3
  rw [← frsF_eq_ptFr I.sel (I.tup a), map_smul] at h5
  intro r
  have h6 := (hc.int _).2 (GlobalTheory.TopStep.mem_stdAt.1 h5 (e r))
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul] at h6
  have h7 : 0 < valuation G.k ((G.ϖ : G.k) ^ (I.cst a).M) := by
    rw [map_pow]
    exact pow_pos ((Valuation.pos_iff _).2 G.ϖ.ne_zero) _
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, ← mul_one (_⁻¹), le_inv_mul_iff₀ h7]
  exact h6

end True

end GlobalTheory.QTw
end
