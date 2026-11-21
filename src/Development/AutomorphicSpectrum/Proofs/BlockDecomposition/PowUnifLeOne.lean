import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial (stdBlocks_ones)

namespace GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_block {N : ℕ} {a : Fin N} (i j : Fin (ones N a)) :
    (1 : Matrix (Fin (ones N a)) (Fin (ones N a)) k) i j = 1 := by
  have : i = j := by
    apply Fin.ext
    have h1 := i.2
    have h2 := j.2
    simp only [ones] at h1 h2
    omega
  subst this
  exact Matrix.one_apply_eq i

theorem mem_Nup_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nup k N := by
  refine mem_unipRad.2 ⟨mem_parab_iff.2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

theorem mem_Nlo_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nlo k N := by
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

end GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

end
