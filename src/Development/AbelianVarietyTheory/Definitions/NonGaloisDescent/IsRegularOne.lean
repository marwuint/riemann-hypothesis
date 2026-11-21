import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.BCen

section Abstract

variable {M V W ι : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def shift (V : Type) [AddCommGroup V] [Module ℂ V] (μ : ι → ℤ) : Module.End ℂ ((ι → ℤ) →₀ V) :=
  Finsupp.lmapDomain V ℂ fun l => l + μ

def univ (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) : Representation ℂ M ((ι → ℤ) →₀ V) where
  toFun g := shift V (deg g).toAdd ∘ₗ Finsupp.mapRange.linearMap (ρ g)
  map_one' := by ext l v; simp [shift]
  map_mul' g h := by ext l v; simp [shift, add_assoc, add_comm (deg g).toAdd]

variable [TopologicalSpace M] [IsTopologicalGroup M]

end Abstract

end GlobalTheory.BCen

end
