import Mathlib

namespace UpperTheory.Reformulated.B.Qi38

noncomputable def Irr {R : Type} [CommRing R] {H : Type} [Group H]
    {n : Type} [Fintype n] [DecidableEq n] (r : H →* Matrix n n R) : Prop :=
  Submodule.span R (Set.range r) = ⊤

@[reducible] noncomputable def modFun {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] :
    Module O (ι → M) :=
  Pi.Function.module ι O M

attribute [local instance] modFun

noncomputable def mapRep {R R' : Type} [CommRing R] [CommRing R'] {H : Type} [Group H]
    {n : Type} [Fintype n] [DecidableEq n] (f : R →+* R') (r : H →* Matrix n n R) :
    H →* Matrix n n R' :=
  f.mapMatrix.toMonoidHom.comp r

private theorem aux {Γ E E' : Type} [Field E] [Field E'] (f : E →+* E') {n : Nat}
    (r : Γ → Matrix (Fin n) (Fin n) E) (hr : Submodule.span E (Set.range r) = ⊤)
    (N : Submodule E' (Fin n → E'))
    (hN : ∀ g v, v ∈ N → ((r g).map f).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  have key : ∀ A : Matrix (Fin n) (Fin n) E, ∀ v ∈ N, (A.map f).mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span E (Set.range r) := by rw [hr]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero =>
      rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]
      exact N.zero_mem
    | add x y _ _ hx hy =>
      rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]
      exact N.add_mem hx hy
    | smul a x _ hx =>
      have h : (a • x).map f = f a • x.map f := by
        ext i j
        simp
      rw [h, Matrix.smul_mulVec]
      exact N.smul_mem _ hx
  refine or_iff_not_imp_left.2 fun hne => ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  have hj' : v j ≠ 0 := hj
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine N.sum_mem fun i _ => ?_
  have h1 := N.smul_mem (w i * (v j)⁻¹) (key (Matrix.single i j 1) v hv)
  have h2 : (w i * (v j)⁻¹) • ((Matrix.single i j (1 : E)).map f).mulVec v = Pi.single i (w i) := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hj']
    · simp [hk]
  rwa [h2] at h1

theorem irr_map {Γ E E' : Type} [Group Γ] [Field E] [Field E']
    (f : E →+* E') {n : ℕ} (r : Γ →* Matrix (Fin n) (Fin n) E) (hr : Irr r)
    (N : Submodule E' (Fin n → E')) (hN : ∀ g v, v ∈ N → ((mapRep f r) g).mulVec v ∈ N) :
    N = ⊥ ∨ N = ⊤ :=
  aux f r hr N hN

end UpperTheory.Reformulated.B.Qi38
