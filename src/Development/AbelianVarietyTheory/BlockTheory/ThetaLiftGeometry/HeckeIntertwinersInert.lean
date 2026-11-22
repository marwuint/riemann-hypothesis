import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Polynomial
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev plF (PP : Pl D.host.E) : HeightOneSpectrum (𝓞 D.host.F) := PP.under (𝓞 D.host.F)

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v', v' ≠ v →
    ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

end
