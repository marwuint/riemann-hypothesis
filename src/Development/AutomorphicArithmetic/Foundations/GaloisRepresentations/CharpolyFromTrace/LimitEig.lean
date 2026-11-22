import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Abstract

variable {k Γ I : Type} [Field k] [Group Γ] {a c : ℕ}

abbrev mat (ρ : Γ →* GL (Fin a) k) (g : Γ) : Matrix (Fin a) (Fin a) k := ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)

def word (ρ : Γ →* GL (Fin a) k) (L : List (Γ × k)) : Matrix (Fin a) (Fin a) k :=
  (L.map fun p => mat ρ p.1 - p.2 • (1 : Matrix (Fin a) (Fin a) k)).prod

def Kills (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (χ : I → k) (ω : Fin c → I → k) : Prop :=
  ∀ (σ : Fin c → I) (s : I), word ρ (List.ofFn (fun b => (j (σ b), ω b (σ b))) ++ [(j s, χ s)]) = 0

def TrSum (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (κ : Fin a → I → k) : Prop :=
  ∀ s, trc ρ (j s) = ∑ i, κ i s

theorem word_nil (ρ : Γ →* GL (Fin a) k) : word ρ [] = 1 := rfl

end Abstract

section Limit

variable {k Γ I : Type} [NormedField k] [Group Γ] {a c : ℕ}

structure Near (r : Γ →* GL (Fin a) k) (H : Subgroup Γ) (ε : ℝ) where

  n : ℕ

  c : Fin n → k

  z : Fin n → k

  ρ : Fin n → (H →* GL (Fin a) k)
  le : ∀ (m : ℕ) (g : H), ‖trc r g - ∑ i, c i * z i ^ m * trc (ρ i) g‖ ≤ ε

end Limit

end UpperTheory.Gal.NearKilling
