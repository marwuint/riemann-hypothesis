import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
import GroundTheory.AutomorphicForms.LocallyConstantCompact
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.AutomorphicForms.WhittakerCells
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import GroundTheory.AutomorphicForms.SmoothRepContragredient
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Matrix

namespace GlobalTheory.BZMir.Whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def WhitLeOne : Prop :=
  ∀ (n : ℕ) (ψ : AddChar k Circle) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → Continuous ψ → ψ ≠ 1 →
      Module.rank ℂ (TwJacquet π (unipB k (Fin n)) (whitChar ψ n)) ≤ 1

end GlobalTheory.BZMir.Whit

end
