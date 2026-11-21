import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)}
  {ng : NgPkg}

def indefiniteDataFamily (U : ∀ w : Dat D Lev, ShimU D G jC ng w) (I : Type) (dat : I → Dat D Lev)
    (hI : ∀ i, (dat i).Indef) : ModuliIntegralCharts.Prov D where
  Dat := I
  rk i := (dat i).N
  jj i := (dat i).j
  jj_range i := ⟨(hI i).1, (hI i).2⟩
  loc w p := (U (dat w)).pad.loc p
  ex w p := (U (dat w)).pad.ex p
  NgC := ng.NgC
  NgC_ne := ng.NgC_ne
  KF := ng.KF
  kfNorm := ng.kfNorm
  pbKF w p := (U (dat w)).pad.pbKF p
  levIn w M := (U (dat w)).pad.levIn M
  Xg w := (U (dat w)).pad.Xg
  bc := @fun w p Z => (U (dat w)).pad.bc p Z
  DivX := @fun w Z => (U (dat w)).pad.DivG Z
  effD := @fun w _ d => (U (dat w)).pad.effD d
  noVertD := @fun w _ d => (U (dat w)).pad.noVertD d
  posBdD := @fun w _ d => (U (dat w)).pad.posBdD d
  ampleOnAbelianBase := @fun w Z n d => (U (dat w)).pad.ampleOnAbelianBase Z n d
  Met w := (U (dat w)).pad.Met
  nefFib := @fun w M => (U (dat w)).pad.nefFibM M
  ampleGen := @fun w M => (U (dat w)).pad.ampleGen M
  limRA := @fun w M => (U (dat w)).pad.limRA M

end Formalism.L2.Geo
