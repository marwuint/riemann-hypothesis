import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCopy
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.BaseLevel

open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel

theorem levFn_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r t s : ℕ} (h : r ≤ n)
    (β) {SG Q : Finset (Pl E)} (P : LevelP SG r ℂ) (cg cg' : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (e : ∀ c, c < s → ∀ PP ∈ SG, cg (c + 1) PP = cg' (c + 1) PP) (g) :
    levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg, xq⟩ g = levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg', xq⟩ g := by
  unfold levFn
  congr 2
  refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c hc => ?_
  exact congrArg (fun f : (kP PP)ˣ →* ℂˣ => f _) (e c (Finset.mem_range.1 hc) PP hPP)

theorem isRes_unique {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem isRes_chiC (h : I.Ok) (j : Fin B.R.m) (PP : Pl (I.rec7 l Z).host.E) (hw : PP ∈ (B.primes X).vGs) :
    IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (chiC I j PP)⁻¹ := by
  intro a k u hk hu
  have ht := (h.ch_tied.mu0 j).atg ⟨PP, hw⟩ k a u hk hu
  have e : ∀ (j : Fin B.R.m) (P : HeightOneSpectrum (𝓞 B.fields.E)) (hw : P ∈ (B.primes X).vGs),
      Formalism.L2.Col.chiP I.Ch P j = I.Ch.chi j ⟨P, hw⟩ := by
    intro j P hw
    unfold Formalism.L2.Col.chiP
    rw [dif_pos hw]
    simp [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi]
  refine Units.ext (Eq.trans ?_ ht.symm)
  have e2 := (chiC_apply I j PP u).trans (congrArg (fun f : _ →* B.LLˣ => B.embLL ((f u : B.LLˣ) : B.LL)) (e j PP hw))
  exact (Units.val_inv_eq_inv_val _).trans ((congrArg (·⁻¹) e2).trans
    ((map_inv₀ B.embLL _).symm.trans (congrArg B.embLL (Units.val_inv_eq_inv_val _).symm)))

set_option maxHeartbeats 2000000 in

theorem topLev_datY (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (cg : ℕ → ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.fields.Kˣ) : B.fields.K))
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ (B.primes X).vGs, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B)) := by
  have hK := hF.what₂
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I ok pins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  obtain ⟨c', -⟩ := F.clsP.y_bij.2 (Quotient.mk'' 1)
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hR := rd_all I hK c'
  have hLb : F.clsP.lev.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  have key := @lev_iff B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ F.clsP.lev hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL hR
    P' (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hH hchi
    (fun i PP a => by
      have e : Formalism.L2.Col.chiP I.Ch PP.1 = Formalism.L2.Col.chiAt I.Ch PP := dif_pos PP.2
      show B.embLL ((Formalism.L2.Col.chiP I.Ch PP.1 i a : B.LLˣ) : B.LL) = _
      rw [e])
  have hc : ∀ c, c < B.R.m → ∀ PP ∈ (B.primes X).vGs, cg (c + 1) PP = chiC I (c + 1 - 1) PP := fun c hc PP hPP =>
    inv_injective (isRes_unique (D := I.rec7 l Z) (hcg ⟨c, hc⟩ PP hPP) (isRes_chiC I l Z ok ⟨c, hc⟩ PP hPP))
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => ?_⟩
  · obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
    exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩
  · refine Eq.trans ?_ ((key _ κ.1 hκ.2).2 κ.2)
    exact congrArg Units.val (levFn_congr (F := B.fields.F) hr 1 P' cg (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hc _)

set_option maxHeartbeats 2000000 in

theorem topLev_levPOf (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (Pg Q : Finset (Pl (I.rec7 l Z).host.E)) (β : GL (Fin (I.rec7 l Z).sp.X'.rank) (EAf (I.rec7 l Z)))
    (hPg : Pg = (B.primes X).vGs) (hQ : Q = ∅) (hβ : β = 1) (eG : R3.Gc B X ≃* G0 Pg (I.rec7 l Z).R.r)
    (hG : ∀ (g : R3.Gc B X) (P : Pl (I.rec7 l Z).host.E) (h : P ∈ (B.primes X).vGs) (h' : P ∈ Pg), eG g ⟨P, h'⟩ = g ⟨P, h⟩)
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ Pg, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B)) := by
  subst hPg hQ hβ
  have he : ∀ g w, eG.symm g w = g w := fun g w =>
    (hG (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  refine topLev_datY I l Z ok pins v F hF hr _ cg ξ (fun g => ?_) (fun g hg => ?_) hcg
  · exact ⟨fun h w => he g w ▸ h w (Set.mem_univ w), fun h w _ => (he g w).symm ▸ h w⟩
  · have e := Formalism.L2.Col.LevFam.chr_apply (X := B.fields) I.Ps ⟨eG.symm g.1, g.2⟩
    refine (congrArg (fun x : B.fields.Kˣ => B.embLL (x : B.fields.K)) e).trans ?_
    show B.embLL ((∏ w, _ : B.fields.Kˣ) : B.fields.K) = _
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact congrArg (fun x => B.embLL (((I.Ps w).lam x : B.fields.Kˣ) : B.fields.K)) (Subtype.ext (he g.1 w))

def PairDataBaseTupleLevelEqualsClassLevel {D : D7} {O : Obj D} (x : R3.TwIn O.ex) {u : D.what₂.Word} (K₀ : ClsPTied u) : Prop :=
  ∀ t : x.T, x.Y.tup t = D.what₂.mu0 →
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))
      (levChi _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))

end GlobalTheory.Fam.BaseLevel

end
