import Mathlib

namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem card_eq (r k : ℕ) (hk : 1 ≤ k) : 2 * r + k + 1 = (k - 1) + (2 * r + 2) := by omega

def param (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun s => Fin.append v (fun i => -b i) (Fin.cast (card_eq r k hk) s)

def cloudIdx (r k : ℕ) (j : Fin (k - 1)) : Fin (2 * r + k + 1) := ⟨j.val, by omega⟩

def nodeIdx (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) : Fin (2 * r + k + 1) :=
  ⟨k - 1 + i.val, by omega⟩

def sign (r k : ℕ) (hk : 1 ≤ k) : Fin (2 * r + k + 1) → Bool :=
  fun s => Fin.append (fun _ : Fin (k - 1) => true)
    (fun i : Fin (2 * r + 2) => decide (Even i.val)) (Fin.cast (card_eq r k hk) s)

@[simp] theorem param_cloud (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (j : Fin (k - 1)) : param r k hk v b (cloudIdx r k j) = v j := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [param, this, Fin.append_left]

@[simp] theorem param_node (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (i : Fin (2 * r + 2)) :
    param r k hk v b (nodeIdx r k hk i) = -b i := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [param, this, Fin.append_right]

@[simp] theorem sign_cloud (r k : ℕ) (hk : 1 ≤ k) (j : Fin (k - 1)) :
    sign r k hk (cloudIdx r k j) = true := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [sign, this, Fin.append_left]

@[simp] theorem sign_node (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) :
    sign r k hk (nodeIdx r k hk i) = decide (Even i.val) := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [sign, this, Fin.append_right]

end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
