import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOkEig

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.L2.DIV Formalism.ConjugateSelfDual Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open GlobalTheory.ExpFrame.GLInhab (oneVec oneVec_ne_zero grp_oneVec one_mem_dualWeyl)

namespace GlobalTheory.ExpFrame.Inhab

variable (l : ℕ) [Fact l.Prime]

def embZ : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])

def act (N : ℕ) (mu : Unit → ℕ → ℕ) (g : GL (Fin N) ℤ_[l]) : Module.End (PadicAlgCl l) (NablaT (PadicAlgCl l) N mu) :=
  embZ l (Matrix.GeneralLinearGroup.det g : ℤ_[l]ˣ) • grp (PadicAlgCl l) N mu fun _ => Matrix.GeneralLinearGroup.map (embZ l) g

def line : CSD ℚ where
  Cl := Unit
  V := ℚ
  ιV := Unit
  bV := Module.Basis.singleton Unit ℚ
  pair := LinearMap.mk₂'ₛₗ _ _ (fun a b => a * b) (fun _ _ _ => add_mul _ _ _)
    (fun c a b => by simp [mul_assoc]) (fun _ _ _ => mul_add _ _ _) (fun c a b => by simp [mul_left_comm])
  Gam := fun _ => Unit
  ρ := fun _ => 1
  Nab := fun _ => Submodule.span (𝓞 ℚ) {1}
  Del := fun _ => Submodule.span (𝓞 ℚ) {1}

def dat (ev : ℕ → ℤ) : BlockDat ℚ Unit Unit where
  S := line
  r := 1
  Pl := Unit
  pl := id
  q _ := 2
  n := 3
  t := 2
  op i := (ev i.2 : ℚ) • 1
  bl := [fun _ => 1]

end GlobalTheory.ExpFrame.Inhab

end
