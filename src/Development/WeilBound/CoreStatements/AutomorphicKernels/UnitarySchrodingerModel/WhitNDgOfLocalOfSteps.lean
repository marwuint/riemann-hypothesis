import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

variable {D : D7} {n : ℕ}

def HeightKInv : Prop :=
  ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ x : G D n, ∀ k ∈ K D n, H (x * k) = H x

def FockKStable : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → ∀ k ∈ K D n, (ω k Φ).1 ∈ fockA θ V n l s

end PositivityTheory.PfSWUS

end
