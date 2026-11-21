import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam

def shimXOfPkg {D : D7} {G : DV.Geo D.what₂.LL} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {N j : ℕ} {Comp : Type} [Fintype Comp] [Nonempty Comp] (cx : CxPkg D.what₂.Tau N j Comp)
    (alg : AlgPkg G D.what₂.Tau N Comp) (pad : PadPkg D N j Comp jC ng) (h : 1 ≤ j ∧ j < N) (lev : Finset ℕ)
    (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h.1
  j_lt := h.2
  lev := lev
  lev_prime := hlev
  Comp := Comp
  vol := cx.vol
  chern := cx.chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N cx.vol P d hd hP
  arDeg := pad.arDeg
  arDeg_homog := pad.arDeg_homog
  arMix := pad.arMix
  arMix_HT := pad.arMix_HT
  arMix_DR := pad.arMix_DR
  CurveHT := pad.CurveHT
  degHT := pad.degHT
  CurveDR := pad.CurveDR
  degDR := pad.degDR
  FibComp := pad.FibComp
  fibInBd := pad.fibInBd
  Pt := pad.Pt
  phiDR := pad.phiDR
  phiMod := pad.phiMod
  phiFr := pad.phiFr
  XC := cx.XC
  rfn := cx.rfn
  rfn_ge := cx.rfn_ge
  hLo := cx.hLo
  hUp := cx.hUp
  hLo_le := cx.hLo_le
  connN := cx.connN
  curvN := cx.curvN
  compOf := cx.compOf
  normDetInf := cx.normDetInf
  compPt := pad.compPt
  normDetT := pad.normDetT
  normDetH := pad.normDetH
  htDetT := pad.htDetT
  ALB := alg.ALB
  arSelf := fun L => ∑ c, alg.arSelfC L c
  arSelfC := alg.arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, alg.geoC L c
  geoC := alg.geoC
  geo_sum := fun _ => rfl
  arVol := alg.arVol
  semipos := alg.semipos
  nefFib := alg.nefFib
  arNef := alg.arNef
  Mbar := alg.Mbar

end GlobalTheory.ShFam
