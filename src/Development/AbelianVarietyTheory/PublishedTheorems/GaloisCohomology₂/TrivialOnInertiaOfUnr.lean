import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace GlobalTheory.GalOfCusp

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix

section Polarization

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {k : Type} [Field k] {a : ℕ}

def IsConjDual (c : Ω ≃+* Ω) (r : G E Ω →* GL (Fin a) k) (μ : G E Ω →* kˣ) : Prop :=
  ∃ P : GL (Fin a) k, ∀ g g' : G E Ω, (∀ x, g' x = c (g (c.symm x))) →
    (r g' : Matrix (Fin a) (Fin a) k) =
      (μ g : k) • ((P : Matrix (Fin a) (Fin a) k) * (r g⁻¹ : Matrix (Fin a) (Fin a) k)ᵀ *
        ((P⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))

variable (E Ω) in

def cycBar (l : ℕ) [Fact l.Prime] : G E Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp (cycZ E Ω l)

end Polarization

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)

def RegAlgShift {a : ℕ} (π : A.CG a) (s : ℝ) : Prop :=
  ∀ τ, (A.infG π τ).Nodup ∧ ∀ z ∈ A.infG π τ, ∃ m : ℤ, z + (s : ℂ) = (m : ℂ) + ((a : ℂ) - 1) / 2

theorem regAlgShift_zero {a : ℕ} (π : A.CG a) : RegAlgShift A π 0 ↔ A.ralg π := by
  rw [A.ralg_def, RegAlgShift]
  simp

variable {A}

variable {i : N.Loc} {a : ℕ} {π : A.CG a} {s : ℝ} {r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))}

end Record

end GlobalTheory.GalOfCusp

end
