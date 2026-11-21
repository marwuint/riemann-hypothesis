import Formalism.LocalToGlobal.CharacterGerms.IsWHLetterMinorK

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem trueT_iff (g : Fin 2) (t' s : ZMod 2) : ((if g = 0 then t' else t' + 1) = s) ↔ t' = trueT g s := by
  unfold trueT
  revert g t' s
  decide

theorem SelfConjugatePlaceSetting.rkF_eq {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) :
    (X o).rkF g s = r (tau o (trueT g s)) := by
  unfold RowData.rkF
  have e : (Finset.univ.filter fun c : IIs r tau o => ((X o).G g).ty (Sum.inl c) = s) =
      Finset.univ.map (Function.Embedding.sigmaMk (β := fun t => Fin (r (tau o t))) (trueT g s)) := by
    ext ⟨t', c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.sigmaMk_apply, H.hty]
    rw [trueT_iff]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Formalism.L2.FormalSeriesBounds.RF
