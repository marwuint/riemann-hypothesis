import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataRRMetric

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badF (R : RealDat D A Ks) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  R.Pg.image fun PP => PP.under (𝓞 D.host.F)

variable {X : DivX D}

end GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

end
