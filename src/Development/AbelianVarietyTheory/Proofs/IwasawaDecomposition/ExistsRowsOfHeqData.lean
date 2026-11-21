import Mathlib
import Formalism.LocalToGlobal.Divisibility.MemberDIV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChKerCCongr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import BuildAid.D3

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem exists_moved {K T : Type} [Field K] {σ : K →+* ℂ} {n : ℕ} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {a b : T} (h : a = b) (E : V ≃ₗ[ℂ] A b) (j : (Fin n → K) →ₛₗ[σ] A a)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ j' : (Fin n → K) →ₛₗ[σ] V, (∀ y, j' y = E.symm (h ▸ j y)) ∧ (LinearIndependent ℂ fun i => j' (Pi.single i 1)) ∧
      Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤ := by
  subst h
  refine ⟨E.symm.toLinearMap.comp j, fun _ => rfl, li.map' E.symm.toLinearMap E.symm.ker, ?_⟩
  have := congrArg (Submodule.map E.symm.toLinearMap) sp
  rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem exists_read_fam {s : ℕ} (hOk : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.Ok s)
    (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) {T : Type} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {b : T} (E : V ≃ₗ[ℂ] A b) (tup : TupF TU → T) (h0 : tup (mu0F TU) = b)
    (inj : Function.Injective tup)
    (j : ∀ t : TupF TU, (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr) → X.K) →ₛₗ[σ] A (tup t))
    (li : ∀ t, LinearIndependent ℂ fun i => j t (Pi.single i 1))
    (sp : ∀ t, Submodule.span ℂ (Set.range fun i => j t (Pi.single i 1)) = ⊤)
    (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ),
      (∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅) y,
        ∃ (F' : (mtildeKGSD W Ch sel t.1).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun),
          HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F')
            (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
              ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
                (lvlIdem P.grp P.chr)).mulVec y)) ∧
          ι (E.symm (ht ▸ j t y)) = zOfRow W Ch sel t.1 hQ P σ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅)
        (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K),
        ∃ hm : (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun,
          ι (E.symm (ht ▸ j t ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) =
            zOfRow W Ch sel t.1 hQ P σ hM ⟨_, hm⟩ := by
  have hQ0 := Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := X) (S := S) sel
  obtain ⟨j', hj, li', sp'⟩ := exists_moved (A := A) h0 E (j (mu0F TU)) (li _) (sp _)
  obtain ⟨ι, hι⟩ := exists_read W Ch sel (mu0F TU).1 hX P hQ0 σ hM j' li' sp'
  refine ⟨ι, fun t e hQ y => ?_, fun t e hQ F => ?_⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι y
    exact ⟨F', hm, heq_of_eq e1, (congrArg ι (hj y)).symm.trans e2⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F)
    have e3 : F' = (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs (mu0F TU) F).1 :=
      ((mtildeKGSD W Ch sel (mu0F TU).1).res (mtildeKOk W Ch sel (mu0F TU).1 hX)).injective
        (e1.trans (evC_res_lvl W Ch sel hX v0 TU Xg S0 xiVal trIv P hOk Zs (mu0F TU) F).symm)
    subst e3
    exact ⟨hm, (congrArg ι (hj _)).symm.trans e2⟩

end Gen

section Main

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem tup_heq (ht : I.IsTw) (U : Set I.ι) (X' : Fields) (hx : X' = B.fields) (Pr : Primes X')
    (sel : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S : Set ℕ) (tup : I.ι → Tup X'.F X'.E X'.K S)
    (cst : ∀ a, LocCst X' (rowSG Pr sel (tup a))) (idx : ∀ a, ChIdx X' Pr B.R (QE sel (tup a : Chr X'.F X'.E X'.K)))
    (h1 : HEq Pr (B.primes X)) (h2 : HEq sel I.sel) (h3 : S = I.S) (h4 : HEq tup I.tup) (h5 : HEq cst I.cst) (h6 : HEq idx I.idx) :
    HEq (fun t : TupU I U => t.1) (fun t => tup (ixOf I U t)) ∧ HEq (fun t : TupU I U => cstT I t.1) (fun t => cst (ixOf I U t)) ∧
      HEq (fun t : TupU I U => idxT I t.1) (fun t => idx (ixOf I U t)) := by
  subst hx h3
  cases h1
  cases h2
  cases h4
  cases h5
  cases h6
  refine ⟨heq_of_eq (funext fun t => (tup_ixOf I t).symm), Function.hfunext rfl fun t t' e => ?_, Function.hfunext rfl fun t t' e => ?_⟩
  · cases e
    rw [← cstT_tup ht, tup_ixOf]
  · cases e
    rw [← idxT_tup ht, tup_ixOf]

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}

theorem iT_heq {t : KerEntTied ex} (hS : I.StdKer l Z t) (τ : (I.rec7 l Z).what₂.Tau) : HEq (t.seam.iT.symm τ) τ := by
  have key : ∀ (X' : Fields) (_ : X' = B.fields) (s : Seam (I.rec7 l Z) X'),
      HEq s (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) → HEq (s.iT.symm τ) τ := by
    intro X' hx s hs
    subst hx
    cases hs
    rfl
  exact key _ hS.X_eq _ hS.seam

abbrev colRecK (t : KerEntTied ex) : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) :=
  colRecC h hp l Z ht hJ t.χ (ker_chi_eq I l Z t) hX U Xg tr

end Main

end GlobalTheory.Mem.R3.SelC

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.SelC

theorem pack_heq {D : D7} (p q : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
      (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D) (_ : Algebra C.Q.c.F D.what₂.LL)
      (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3), G0 R.Pg D.R.r ≃* G0g D.nd) (e : p = q) :
    letI := p.2.1; letI := p.2.2.1; letI := p.2.2.2.2.2.2.2.2.1; letI := q.2.1; letI := q.2.2.1; letI := q.2.2.2.2.2.2.2.2.1
    (p.1 = q.1 ∧ HEq p.2.1 q.2.1 ∧ p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧ p.2.2.2.2.2.1 = q.2.2.2.2.2.1 ∧
      HEq p.2.2.2.2.2.2.1 q.2.2.2.2.2.2.1) ∧
    (HEq p.2.2.2.2.2.2.2.2.2.2.1.P0 q.2.2.2.2.2.2.2.2.2.2.1.P0 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ0 q.2.2.2.2.2.2.2.2.2.2.1.ψ0 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.P1 q.2.2.2.2.2.2.2.2.2.2.1.P1 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ1 q.2.2.2.2.2.2.2.2.2.2.1.ψ1 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.Dc q.2.2.2.2.2.2.2.2.2.2.1.Dc ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.Sp q.2.2.2.2.2.2.2.2.2.2.1.Sp) ∧
    HEq (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1) (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1)).Mem =
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)).Mem := by
  subst e
  exact ⟨⟨rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl⟩, ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩, HEq.rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem heq_app {A M M' : Type} (e : M = M') {f : A → M} {g : A → M'} (h : HEq f g) (u : A) : HEq (f u) (g u) := by
  subst e
  cases h
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}

variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.Mem.R3.SelC

end
