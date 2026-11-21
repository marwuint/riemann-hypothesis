import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc' : Nat.card (IsLocalRing.ResidueField O) = q ^ 2 := hc
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  have h0 : ((q ^ 2 : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← hc', Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  have hle : Valued.v (2 : L) ≤ 1 := (2 : O).2
  by_contra hne
  have hlt : Valued.v (2 : L) < 1 := lt_of_le_of_ne hle hne
  have hm : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h2' : (2 : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (2 : O)).2 hm
    rwa [map_ofNat] at this
  obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
  rw [hk] at h0
  push_cast at h0
  rw [h2'] at h0
  simp at h0

def bb (σ : L →+* L) (δ : L) (x y : L) : L := (δ * (σ y * x) + σ (δ * (σ y * x))) / 2

def rho0 (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) (x : L) : Module.End ℂ (L → ℂ) where
  toFun φ := fun w => ψ (bb σ δ w x) * φ (w + x)
  map_add' φ φ' := by funext w; simp [mul_add]
  map_smul' c φ := by funext w; simp [mul_left_comm]

open Classical in

def vac0 (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : L → ℂ := fun w => if w ∈ intL L then 1 else 0

def Mod (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) : Submodule ℂ (L → ℂ) := Submodule.span ℂ (Set.range fun x => rho0 σ δ ψ x (vac0 L))

section Main

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ}

abbrev U1 (σ : L →+* L) : Type := UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)

def ent (g : U1 σ) : L := ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) 0 0

theorem weil_rep_zero (φ : L → ℂ) : rho0 σ δ ψ 0 φ = φ := by
  funext w
  show ψ (bb σ δ w 0) * φ (w + 0) = φ w
  simp [bb]

variable (σ δ ψ) in

def vac : Mod σ δ ψ := ⟨vac0 L, Submodule.subset_span ⟨0, weil_rep_zero _⟩⟩

end Main

end GlobalTheory.Hk3.Inh

end
