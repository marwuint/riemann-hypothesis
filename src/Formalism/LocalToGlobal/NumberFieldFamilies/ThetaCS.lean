import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfF D) (V : HSp D)

def Smo (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

variable {θ V}

theorem Smo.add {φ φ' : GA D V → ℂ} (h : Smo θ V φ) (h' : Smo θ V φ') : Smo θ V (φ + φ') :=
  fun k τs Xs hX g => (h k τs Xs hX g).add (h' k τs Xs hX g)

end Formalism.L2.Fam.ThC

end
