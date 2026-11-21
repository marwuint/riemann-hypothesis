import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.ConjMonomial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [ones] at this
    omega
  simp [ones, hi]

theorem tor_offDiag {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  have h := leviEmb_apply_ne k (stdBlocks (ones N) (sum_ones N)) s hij
    (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N j))
  rwa [stdBlocks_ones, stdBlocks_ones] at h

theorem mem_tor_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  have hd : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    intro i h0
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro l _
      by_cases hl : i = l
      · subst hl
        rw [h0, zero_mul]
      · rw [h i l hl, zero_mul]
  refine ⟨fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
    (Units.mk0 _ (hd a)), ?_⟩
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 := leviEmb_apply_same k (stdBlocks (ones N) (sum_ones N))
      (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
        (Units.mk0 _ (hd a))) i (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N i))
    rw [stdBlocks_ones] at h1
    rw [h1]
    simp [Matrix.algebraMap_matrix_apply]
  · have h1 := leviEmb_apply_ne k (stdBlocks (ones N) (sum_ones N))
      (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
        (Units.mk0 _ (hd a))) hij (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N j))
    rw [stdBlocks_ones, stdBlocks_ones] at h1
    rw [h i j hij]
    exact h1

end GlobalTheory.CompanionTheory.LbElem.ConjMonomial

end
