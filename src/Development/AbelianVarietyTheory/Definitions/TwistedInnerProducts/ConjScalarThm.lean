import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

variable {D : D7}

def RelLab (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Prop :=
  (Formalism.DivisionValues.conjPl P ≠ P ∧ ∃ k, k ≤ V.rank ∧ d = splitLab V.rank k) ∨ (Formalism.DivisionValues.conjPl P = P ∧ GlobalTheory.Hk3.IsLab V P d)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Eig

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def EigF {W : Type} [AddCommGroup W] [Module ℂ W] (a : Pl D.host.E → List ℤ → ℂ) (Φ : Bridge.Gf (Vc D i) → W) : Prop :=
  ∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → RelLab (Vc D i) P d → GlobalTheory.Hk3.hkF (Vc D i) P (Finsupp.single d 1) Φ = a P d • Φ

def EigK (a : Pl D.host.E → List ℤ → D.what₂.LL) (x : A.fam.amb.FL i A.μ0) : Prop :=
  EigF R i (fun P d => D.what₂.embLL (a P d)) ((R.HV i A.μ0).e (R.jV i A.μ0 x))

end Eig

end GlobalTheory.ConjScalar

end
