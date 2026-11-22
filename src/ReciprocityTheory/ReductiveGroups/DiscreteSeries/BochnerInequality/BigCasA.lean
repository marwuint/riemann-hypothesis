import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Slots

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    (ofCoords k f x) κ = f κ x := rfl

theorem mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  show (ofCoords k _ F) κ = _
  rw [ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> rfl

theorem mem_ncV_iff {k : ℕ} {F : Big n k M} : F ∈ ncV ε V k ↔
    ∀ κ : Fin k → Fin n × Fin n, ((∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ ∈ V) ∧
      ((¬ ∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ = 0) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun κ => ?_
  split_ifs with h <;> simp [h] <;> rfl

def positionPerm {k : ℕ} (i : Fin k) (τ : Equiv.Perm (Fin n × Fin n)) :
    Equiv.Perm (Fin k → Fin n × Fin n) where
  toFun κ := Function.update κ i (τ (κ i))
  invFun κ := Function.update κ i (τ.symm (κ i))
  left_inv κ := by simp
  right_inv κ := by simp

theorem factorAd_mem_ncV {k : ℕ} (i : Fin k) {a b : Fin n} (hab : ε a = ε b) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : factorAd k i a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  rcases hx : κ i with ⟨x, y⟩
  simp only [factorAd_apply, hx]
  constructor
  · intro hκ
    have hxy : ε x ≠ ε y := by simpa [hx] using hκ i
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs with h <;> try exact Submodule.zero_mem _
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [← hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
  · intro hκ
    push Not at hκ
    obtain ⟨j, hj⟩ := hκ
    have key : ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → (¬ ∀ l, ε ((Function.update κ i p) l).1 ≠
        ε ((Function.update κ i p) l).2) := by
      intro p hp h
      by_cases hji : j = i
      · subst hji; exact h j (by simpa using hp)
      · exact h j (by rw [Function.update_of_ne hji]; exact hj)
    have hxy : j = i → ε x = ε y := by intro hji; subst hji; simpa [hx] using hj
    have hc : ∀ p : Fin n × Fin n, (j = i → ε p.1 = ε p.2) → F (Function.update κ i p) = 0 := by
      intro p hp
      by_cases hji : j = i
      · exact (hF _).2 (key p (hp hji))
      · refine (hF _).2 fun h => h j ?_
        rw [Function.update_of_ne hji]; exact hj
    rw [ite_eq_right_iff.2 ?_, ite_eq_right_iff.2 ?_, sub_zero]
    · intro h; subst h; exact hc _ fun hji => by show ε x = ε a; rw [hxy hji, ← hab]
    · intro h; subst h; exact hc _ fun hji => by show ε b = ε y; rw [← hab, hxy hji]

theorem mAct_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) {a b : Fin n} (hab : ε a = ε b)
    {F : Big n k M} (hF : F ∈ ncV ε V k) : mAct E k a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  simp only [mAct_apply]
  exact ⟨fun h => hV a b hab _ ((hF κ).1 h), fun h => by rw [(hF κ).2 h, map_zero]⟩

end Slots

end ReciprocityTheory.ChartRestriction.DS.BigCasimir
