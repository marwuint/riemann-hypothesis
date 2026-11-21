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

def IsInertPl (PP : Pl D.host.E) : Prop :=
  Formalism.UG.IsInertAt D.host.F D.host.E (plF PP) PP

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v', v' ≠ v →
    ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levX (R : RealDat D A Ks) (t : T) : Subgroup (Bridge.Gf D.sp.X') := (levEnv D.sp.X' R.βX (R.datXt t)).J

def IsInertDC (R : RealDat D A Ks) (t : T) (PP : Pl D.host.E) (x : Bridge.Gf D.sp.X') (B : Finset (Bridge.Gf D.sp.X')) : Prop :=
  IsInertPl PP ∧ PP ∉ R.Sb ∧ PP ∉ R.Q t ∧ LocAt D.sp.X' (plF PP) x ∧ (∀ b ∈ B, LocAt D.sp.X' (plF PP) b) ∧
    Bridge.IsDC (levX R t) x B

abbrev InertIx (R : RealDat D A Ks) (t : T) : Type :=
  {a : Pl D.host.E × Bridge.Gf D.sp.X' × Finset (Bridge.Gf D.sp.X') // IsInertDC R t a.1 a.2.1 a.2.2}

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

end
