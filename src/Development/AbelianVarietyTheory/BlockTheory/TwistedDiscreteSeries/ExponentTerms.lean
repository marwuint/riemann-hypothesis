import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lattices
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def MapsInto (x : Matrix κ ι k) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ v ∈ M', x *ᵥ v ∈ M

def InjMod (ϖ : 𝒪[k]) (x : Matrix κ ι k) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  MapsInto x M' M ∧ ∀ v ∈ M', x *ᵥ v ∈ ϖ • M → v ∈ ϖ • M'

def act (g : GL ι k) (M : Submodule 𝒪[k] (ι → k)) : Submodule 𝒪[k] (ι → k) :=
  M.map ((Matrix.mulVecLin g.val).restrictScalars 𝒪[k])

def stdLat (k : Type) [Field k] [ValuativeRel k] (ι : Type) : Submodule 𝒪[k] (ι → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)

def IsReps (ϖ : 𝒪[k]) (M : Submodule 𝒪[k] (ι → k)) (T : Finset (ι → k)) : Prop :=
  (∀ t ∈ T, t ∈ M) ∧ ∀ v ∈ M, ∃! t, t ∈ T ∧ v - t ∈ ϖ • M

def SuppIn (Ψ : Matrix κ ι k → ℂ) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ x, Ψ x ≠ 0 → MapsInto x M' M

def PeriodicMod (ϖ : 𝒪[k]) (Ψ : Matrix κ ι k → ℂ) (M' : Submodule 𝒪[k] (ι → k))
    (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ x y, MapsInto y M' M → Ψ (x + (ϖ : k) • y) = Ψ x

end Lattices

section Chain
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def aux (k : Type) [Field k] (n : Type) [DecidableEq n] {c : ℕ} (i : Fin c) : n ⊕ Fin c → k :=
  Pi.single (Sum.inr i) 1

def inX (k : Type) [Field k] [ValuativeRel k] (n : Type) (c : ℕ) : (n → k) →ₗ[𝒪[k]] (n ⊕ Fin c → k) where
  toFun v := Sum.elim v 0
  map_add' v w := by ext (r | r) <;> simp
  map_smul' a v := by ext (r | r) <;> simp

def chainLat (ϖ : 𝒪[k]) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔
    Submodule.span 𝒪[k] (Set.range fun i : Fin c => (ϖ : k) ^ (i.val + 1) • aux k n i)

def Yle (k : Type) [Field k] [ValuativeRel k] (n : Type) (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {v | ∀ l : Fin c, i < l.val + 1 → v (Sum.inr l) = 0}
  add_mem' hv hw l hl := by simp [hv l hl, hw l hl]
  zero_mem' l _ := rfl
  smul_mem' a v hv l hl := by simp [hv l hl]

def pt (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  basePt c x₀ + Matrix.of fun r s =>
    Sum.elim (fun _ => 0) (fun j : Fin (c + 1) => Fin.cases 0 (fun i => y i r) j) s

variable [MeasurableSpace k] [BorelSpace k]

def OneClass (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (hc : 1 ≤ c) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)), Submodule.IsLattice k Λ →
    ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Ψ (chainLat ϖ (c + 1) L') Λ → PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') Λ →
      opE ψ ν 1 Ψ ≠ 0 →
        (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) =
          Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) ∧
        (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ ∧
        (∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c))) ∧
        ∃ r ∈ R k n c 1, Λ = act r (chainLat ϖ c (stdLat k n))

def OneCoset (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (c : ℕ) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  (∀ (μ : kˣ →* ℂˣ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Φ (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) →
      PeriodicMod ϖ Φ (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) →
      ∀ (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
        act h' (chainLat ϖ (c + 1) L') = chainLat ϖ (c + 1) L' →
        opE ψ ν 1 (om μ h' h Φ) ≠ 0 →
          ∃ r ∈ R k n c 1, ∃ t : GL (n ⊕ Fin c) k,
            act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) ∧ h = r * t) ∧
  ∀ J : Subgroup (GL (n ⊕ Fin c) k),
    (∀ j ∈ J, act j (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n)) →
    (∀ j : GL (n ⊕ Fin c) k, act j (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) →
      MapsInto (j.val - 1) (chainLat ϖ c (stdLat k n)) (ϖ • chainLat ϖ c (stdLat k n)) → j ∈ J) →
    ∃ T : Finset (GL (n ⊕ Fin c) k),
      (∀ t ∈ T, act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n)) ∧
      ∀ h : GL (n ⊕ Fin c) k,
        (∃ r ∈ R k n c 1, ∃ t : GL (n ⊕ Fin c) k,
            act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) ∧ h = r * t) ↔
          ∃ r ∈ R k n c 1, ∃ t ∈ T, ∃ j ∈ J, h = r * t * j

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
