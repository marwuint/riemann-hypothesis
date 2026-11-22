import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData
open scoped TensorProduct

namespace GlobalTheory.DimPartsTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Matching (D : D7) (Pg : Finset (Pl D.host.E)) where
  plg : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg
  mem : ∀ PP : ↥Pg, ((D.host.g (plg.symm PP).1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal
  nconj : ∀ PP PP' : ↥Pg, ¬ IsConjPl D.host PP.1 PP'.1

def Matching.toG0 {Pg : Finset (Pl D.host.E)} (μ : Matching D Pg) (γ : G0g D.nd) : G0 Pg D.R.r := fun PP =>
  Matrix.GeneralLinearGroup.map (resMap (D.host.g (μ.plg.symm PP).1) PP.1 (μ.mem PP)) (γ (μ.plg.symm PP))

def Matching.eCoef {Pg : Finset (Pl D.host.E)} (μ : Matching D Pg) : G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain μ.toG0 D.ntypes.e0.coeff

end GlobalTheory.DimPartsTest

end
