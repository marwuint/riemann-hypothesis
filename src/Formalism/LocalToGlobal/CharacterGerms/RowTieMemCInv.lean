import Formalism.LocalToGlobal.CharacterGerms.RowTieMemC
import Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

theorem rowShift_C (σ : T) (i i' : Fin (r σ)) (t z : C) :
    rowShift r n C σ i i' t (MvPolynomial.C z) = MvPolynomial.C z := (rowShift r n C σ i i' t).commutes z

variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)

theorem shift_same (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (t : C)
    (ρ : Fin N) (c : Fin N') (h : ¬ (σ = σ0 ∧ c.val = i.val)) :
    rowShift r n C σ i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) := by
  rw [hΦ, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, rowShift_C, rowShift_X, hlt, if_neg]
  intro e
  apply h
  exact ⟨(congrArg (fun x : T × ℕ × Fin n => x.1) e).symm, congrArg (fun x : T × ℕ × Fin n => x.2.1) e⟩

theorem shift_add (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (i i' : Fin (r σ0)) (t : C)
    (ρ : Fin N) (c c' : Fin N') (hc : c.val = i.val) (hc' : c'.val = i'.val) :
    rowShift r n C σ0 i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) + MvPolynomial.C t * Φ (X (ρ, c')) := by
  rw [hΦ, hΦ, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h2 : (lt (ρ, c) q).2.2 = colf ρ q := congrArg (fun x : T × ℕ × Fin n => x.2.2) (hlt ρ c q)
  have h1 : keyL (lt (ρ, c) q) = (σ0, i.val, (lt (ρ, c) q).2.2) := by rw [hlt, hc, h2]
  rw [map_mul, rowShift_C, rowShift_X, if_pos h1]
  have h3 : (⟨σ0, i', (lt (ρ, c) q).2.2⟩ : Letter T r n) = lt (ρ, c') q := by
    apply keyL_inj
    rw [hlt, hc', h2]
    rfl
  rw [h3]
  ring

theorem rowShift_minor_lin (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (Φ (minorK C N N' k)) = Φ (minorK C N N' k) := by
  unfold minorK
  split_ifs with h
  · set A : Matrix (Fin k) (Fin k) (MvPolynomial (Letter T r n) C) :=
      Matrix.of fun b c => Φ (X (Fin.castLE h.1 b, Fin.castLE h.2 c)) with hA
    have e1 : Φ (Matrix.of fun b c : Fin k =>
        (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') C)).det = A.det := by
      rw [AlgHom.map_det]
      congr 1
    rw [e1, AlgHom.map_det]
    by_cases hc : σ = σ0 ∧ i.val < k
    · obtain ⟨rfl, hik⟩ := hc
      have hi' : i'.val < i.val := hi
      let ci : Fin k := ⟨i.val, hik⟩
      let ci' : Fin k := ⟨i'.val, lt_trans hi' hik⟩
      have hne : ci ≠ ci' := by
        intro e
        have h3 : ci.val = ci'.val := congrArg Fin.val e
        have h4 : i.val = i'.val := h3
        omega
      have e2 : (rowShift r n C σ i i' t).mapMatrix A =
          A.updateCol ci (fun b => A b ci + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b ci') := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        simp only [hA, Matrix.of_apply]
        by_cases hcc : c = ci
        · subst hcc
          rw [if_pos rfl, smul_eq_mul]
          exact shift_add Φ σ w lt colf hΦ hlt i i' t _ _ _ rfl rfl
        · rw [if_neg hcc]
          refine shift_same Φ σ w lt colf hΦ hlt σ i i' t _ _ ?_
          rintro ⟨_, e⟩
          exact hcc (Fin.ext e)
      rw [e2, Matrix.det_updateCol_add_smul_self A hne]
    · have e2 : (rowShift r n C σ i i' t).mapMatrix A = A := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply]
        simp only [hA, Matrix.of_apply]
        refine shift_same Φ σ0 w lt colf hΦ hlt σ i i' t _ _ ?_
        rintro ⟨e0, e⟩
        apply hc
        refine ⟨e0, ?_⟩
        have : c.val = i.val := e
        omega
      rw [e2]
  · simp

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def trueT (g : Fin 2) (s : ZMod 2) : ZMod 2 := if g = 0 then s else s + 1

end Fam

end Formalism.L2.FormalSeriesBounds.RF
