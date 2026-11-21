import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section
namespace GlobalTheory.HeightCounting.Up.RealOfReading

open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

def realOfRead {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    {cf : CharFrame D} {nch : NChoice D} (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd)
    (labPi : E.Pi → A3.A.fam.base.Ix) (hbase : R.BaseW F)
    (htup : ∀ μ, Used0 D μ → R.toLevCh.xiH (Y.tupT μ) = tp.xi μ) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP) :
    GlobalTheory.NJoin.RealAt D cf nch tp where
  G := G
  Pl0 := Pl0
  T := T
  A := A3.A
  Ks := Ks
  R := R
  F := F
  tupT := Y.tupT
  hm := Y.hm
  hTop := Y.hTop
  hinj := Y.hinj
  X0 := X0
  Ish := Y.Ish
  I0 := Y.Iz
  IL := Y.IL
  K := Y.Kc
  Xd := Xd
  E := E
  labPi := labPi
  PY := Y.PY
  PW := Y.PW
  eFT := Y.eFT
  piOf := fun _ _ _ => 0
  ι := Y.ιW
  Tp := hC.symm ▸ tp
  cfEq := hC
  tpEq := by subst hC; rfl
  recR := by
    subst hC
    exact ⟨hbase, Y.tied, Y.prtE, Y.prtE0, Y.prtWE, Y.xi, htup,
      fun w => by rw [Y.muAt w, Y.tupT_tup], Y.isomFin, Y.frameMatch⟩
  given := hg
  full := hf

end GlobalTheory.HeightCounting.Up.RealOfReading
end
