import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralSeries

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Series

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def fock (B : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (P : PolF D (Wc D i).rank (Vc D i).rank) : WO (Vc D i) (Wc D i) → ℂ :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) B (onb (R.MW i (sg0 D A))) f P

end Series

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralSeries
