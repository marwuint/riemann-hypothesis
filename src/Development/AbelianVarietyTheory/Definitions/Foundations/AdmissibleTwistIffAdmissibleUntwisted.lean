import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ChiK
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def admitted {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) : Prop :=
  1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = mat W s *ᵥ pr b) ∧
    ∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b

def unTw {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (χ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l :=
  tw W (cycBar ℚ Ω l ^ e * χ⁻¹)

end GlobalTheory.K4
