import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Red

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Emb (x y z : IrrGL k) : Prop :=
  ∃ (hd : ∑ a, (![y, z] a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr ![y, z] hd)), Function.Injective f

def up (ρ : IrrGL k) : Set (IrrGL k) := {y | ∃ n : ℕ, y = ρ.nu (n : ℂ)}

end UpperTheory.Lit.Red

end
