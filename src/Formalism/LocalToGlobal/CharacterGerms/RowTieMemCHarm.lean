import Formalism.LocalToGlobal.CharacterGerms.PderivSubGOff

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Fam

theorem mem_vars_blkProdG {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (I o) (J o)} {F : ∀ o, Flag (X o)} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n} {b : Fin n} {o : Orb} {w : WV (I o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO I) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  first
  | unfold blkProd at hx
  | simp only [blkProd] at hx
  first
  | unfold toAll at hx
  | simp only [toAll] at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨x, hx1, hx2⟩ := h3
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at hx2
  obtain ⟨hb, ho, hw⟩ := hx2
  subst ho
  obtain rfl := eq_of_heq hw
  subst hb
  exact hx1

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}

end Fam

end Formalism.L2.FormalSeriesBounds.RF
