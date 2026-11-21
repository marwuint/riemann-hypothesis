import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PinnedIntegrability

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure Pinned : Prop where
  lev : R.toLevCh.Is A.μ0
  inf : R.models_inf
  vpos : RealDat.models_vpos (D := D)
  cV : R.models_cV
  HV : R.models_HV
  νV : R.models_νV
  BV : R.models_BV
  order : R.models_order
  ωP : R.thP_ωP
  vP : R.thP_vP
  pt_theta : R.thP_pt_theta
  ioP : R.thP_ioP

end

end GlobalTheory.IndefiniteRowSideFullHecke.PinnedIntegrability

end
