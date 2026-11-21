import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7}

def IsRealParam {m n k : ℕ} (L : (Fin k → ℝ) →+ Mx D m n) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

structure IsSchwartzBruhat {m n : ℕ} (φ : Mx D m n → ℂ) : Prop where

  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, φ (x + u) = φ x

  supp : ∃ K : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, φ x ≠ 0 → x.map (finPart D) ∈ K

  schwartz : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), IsRealParam L → Function.Injective L →
    ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t)

end GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

end
