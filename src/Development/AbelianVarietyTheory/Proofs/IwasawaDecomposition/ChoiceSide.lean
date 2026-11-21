import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : GlobalTheory.Published.LocalLanglandsGL}

def Mv.sideA {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : SideA D cf jE) : SideA m.D (m.cf cf) jE := @_root_.GlobalTheory.HeightCounting.SideA.mk (_) (_) (_)
    (bare := (A.bare))
    (wdT := (A.wdT))
    (lab := (A.lab))
    (chr := @_root_.GlobalTheory.HeightCounting.CharSide.mk (_) (_)
      (e1 := (A.chr.e1))
      (unr_iff := (A.chr.unr_iff))
      (frob := (A.chr.frob))
      (tw := (A.chr.tw))
      (infG := (A.chr.infG))
      (csd := (A.chr.csd))
      (etaT := (A.chr.etaT))
      (etaTinv := (A.chr.etaTinv))
      (plGw := (A.chr.plGw)))
    (row := @_root_.GlobalTheory.HeightCounting.RowSide.mk (_)
      (locR := (A.row.locR))
      (satR := (A.row.satR))
      (lab_eq := (A.row.lab_eq)))
    (pl := @_root_.GlobalTheory.HeightCounting.PlSide.mk (_)
      (ι := (A.pl.ι))
      (ι_w := (A.pl.ι_w))
      (plB := (A.pl.plB))
      (plB_eq := (A.pl.plB_eq))
      (plκ := (A.pl.plκ)))
    (iota := (A.iota))
    (wd := @_root_.GlobalTheory.HeightCounting.WDSide.mk (_) (_)
      (wdOf := (A.wd.wdOf))
      (wdOf_dim := (A.wd.wdOf_dim))
      (wdOf_unr := (A.wd.wdOf_unr))
      (wdOf_frob := (A.wd.wdOf_frob))
      (wdOf_ine := (A.wd.wdOf_ine))
      (wdOf_mono0 := (A.wd.wdOf_mono0))
      (IsCrysW := (A.wd.IsCrysW))
      (IsPotCrysW := (A.wd.IsPotCrysW))
      (IsdRW := (A.wd.IsdRW))
      (jumpsW := (A.wd.jumpsW))
      (wdOf_unrL := (A.wd.wdOf_unrL))
      (wdOf_mono0L := (A.wd.wdOf_mono0L))
      (away := (A.wd.away))
      (above := (A.wd.above))
      (loc := (A.wd.loc)))
    (grp := @_root_.GlobalTheory.HeightCounting.GrpSide.mk (_)
      (tA := (A.grp.tA))
      (tκ := (A.grp.tκ))
      (teichC_def := (A.grp.teichC_def))
      (ζ := (A.grp.ζ))
      (ζ_gen := (A.grp.ζ_gen))
      (O := (A.grp.O))
      (eSer_def := (A.grp.eSer_def))
      (kv := (A.grp.kv))
      (tg_tame := (A.grp.tg_tame))
      (O_equiv := (A.grp.O_equiv))
      (O_tw := (A.grp.O_tw)))
    (par := @_root_.GlobalTheory.HeightCounting.ParSide.mk (_) (_)
      (eM := (A.par.eM))
      (eM_K := (A.par.eM_K))
      (eP := (A.par.eP))
      (locPar_def := (A.par.locPar_def)))
    (au := @_root_.GlobalTheory.HeightCounting.AUSide.mk (_)
      (cls := (A.au.cls))
      (surj := (A.au.surj))
      (iso := (A.au.iso))
      (mult := (A.au.mult))
      (sph := (A.au.sph))
      (sat := (A.au.sat))
      (clsWt := (A.au.clsWt))
      (surjWt := (A.au.surjWt))
      (isoWt := (A.au.isoWt))
      (wt := (A.au.wt))
      (infW := (A.au.infW))
      (locUnr := (A.au.locUnr))
      (locPol := (A.au.locPol)))
    (chiT := (A.chiT))

theorem Mv.au {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} (x : AUTrue hL D A.wdT A.au) : AUTrue hL m.D (m.sideA A).wdT (m.sideA A).au := (x)
theorem Mv.row {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {rep} (x : RowTrue hL D rep (fun σ w ↦ (A.wdT.e w) (A.row.locR σ w)) A.row.satR) : RowTrue hL m.D rep (fun σ w ↦ ((m.sideA A).wdT.e w) ((m.sideA A).row.locR σ w)) (m.sideA A).row.satR := (x)

section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.mtInput (x : MtInput D M tp.tup C.Q) : MtInput m.D (m.mt M) (m.tp tp).tup (m.ch C).Q := @_root_.GlobalTheory.HeightCounting.MtInput.mk (_) (_) (_) (_)
    (prod := (x.prod))
    (para := (x.para))
    (uni := (x.uni))
    (hyp := (x.hyp))
    (wt := (x.wt))
    (rat := (x.rat))
    (int := (x.int))
    (full := (x.full))

def Mv.ratIn {S} (x : RatIn D S) : RatIn m.D S := @_root_.GlobalTheory.HeightCounting.RatIn.mk (_) (_)
    (Sb := (x.Sb))
    (rho := (x.rho))
    (chi := (x.chi))
    (ks := (x.ks))
    (fd := (x.fd))
    (mk_fg := (x.mk_fg))
    (hL := (x.hL))
    (hs := (x.hs))
    (hL_zero := (x.hL_zero))
    (θ := (x.θ))
    (θ_ne := (x.θ_ne))
    (eig := (x.eig))
    (span := (x.span))
    (hL_int := (x.hL_int))
theorem Mv.rowDepth {rep} (x : RowDepth D rep) : RowDepth m.D rep := (x)
end

def Mv.host (x : HostTied D) : HostTied m.D := @_root_.Formalism.L2.Host.HostTied.mk (_)
    (fr := (x.fr))
    (jLL := (x.jLL))
    (embLL := (x.embLL))
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}

def Mv.chrN (x : NCharTied D cf C tp) : NCharTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NCharTied.mk (_) (_) (_) (_)
    (e1 := (x.e1))
    (unr_iff := (x.unr_iff))
    (frob := (x.frob))
    (tw := (x.tw))
    (infG := (x.infG))
    (csd := (x.csd))
    (muC := (x.muC))
    (etaT := (x.etaT))
    (etaTinv := (x.etaTinv))
    (plGw := (x.plGw))
theorem Mv.chrGal (x : NGalChrTied D cf C tp) : NGalChrTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NGalChrTied.mk (_) (_) (_) (_)
    (psi_is := (x.psi_is))
    (psiL := (x.psiL))
    (deltaRead := (x.deltaRead))
theorem Mv.oSplit (x : GlobalTheory.SplitCoef.OSplit D) : GlobalTheory.SplitCoef.OSplit m.D := (x)
theorem Mv.large (x : GlobalTheory.CoefDuty.Large D) : GlobalTheory.CoefDuty.Large m.D := (x)
theorem Mv.bkLaw (x : BkLaw D) : BkLaw m.D := (x)

def Mv.omFrame (x : Formalism.L2.OmFrame D) : Formalism.L2.OmFrame m.D := @_root_.Formalism.L2.OmFrame.mk (_)
    (jE := (x.jE))
    (eOm := (x.eOm))
    (comm := (x.comm))
end

theorem Mv.pack_pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) {cf : CharFrame D₀} {C : NChoice D₀} (tp : TupTied D₀ cf C) :
    (⟨m.D, m.cf (cfL L cf), m.ch (chL L C), m.tp (tpL L tp)⟩ : Σ D : D7, Σ c : CharFrame D, Σ C : NChoice D, TupTied D c C) =
      ⟨withLoc (m.pre.loc L), cfL (m.pre.loc L) (m.pre.cf cf), chL (m.pre.loc L) (m.pre.ch C), tpL (m.pre.loc L) (m.pre.tp tp)⟩ :=
  (@Eq.refl (@Sigma D7 fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@Sigma.mk D7 (fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@D (@withLoc D₀ L) m) (@Sigma.mk (CharFrame (@D (@withLoc D₀ L) m)) (fun c ↦ @Sigma (NChoice (@D (@withLoc D₀ L) m)) fun C ↦ TupTied (@D (@withLoc D₀ L) m) c C) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) (@Sigma.mk (NChoice (@D (@withLoc D₀ L) m)) (fun C ↦ TupTied (@D (@withLoc D₀ L) m) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) C) (@ch (@withLoc D₀ L) m (@chL D₀ L C)) (@Mv.tp (@withLoc D₀ L) m (@cfL D₀ L cf) (@chL D₀ L C) (@tpL D₀ L cf C tp))))))

end GlobalTheory.LayerMove
end
