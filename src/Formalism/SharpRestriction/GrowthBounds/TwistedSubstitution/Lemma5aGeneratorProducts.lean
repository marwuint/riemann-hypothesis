import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aMonomial

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

def pairSet (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th : ℤ → ℝ) : Set (SegRing O r K) :=
  {P | ∃ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
      A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters j} ∧
      G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} ∧
      (∀ x ∈ F.letters j, ¬ F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (th x)) ∧
      P = plEmb O r K A * nmEmb O r K G}

section Multi

variable (p : ℕ) {n' m r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) (F : Frames n' r)

def symG (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O))
    (rename (castV hk) ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l 1) * monomial ga 1)

theorem symG_update (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (y : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) y) =
      MvPolynomial.map (algebraMap O (KK O))
        (rename (castV hk) (phSeg O K p F (k : ℤ) y *
          ((∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (x j)) * monomial l 1)) * monomial ga 1) := by
  unfold symG
  have he : ∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (Function.update x (k : ℤ) y j) =
      ∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (x j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by exact_mod_cast Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase _ _ hk', he, Function.update_self, mul_assoc]

theorem symG_zero (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) : symG p O hk F l ga (Function.update x (k : ℤ) 0) = 0 := by
  rw [symG_update p O hk F l ga x k hk' 0]
  simp

theorem symG_add (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (a b : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) (a + b)) =
      symG p O hk F l ga (Function.update x (k : ℤ) a) + symG p O hk F l ga (Function.update x (k : ℤ) b) := by
  rw [symG_update p O hk F l ga x k hk', symG_update p O hk F l ga x k hk',
    symG_update p O hk F l ga x k hk', map_add, add_mul, map_add, add_mul, map_add]

theorem symG_smul (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (c : O) (a : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) (c • a)) =
      algebraMap O (KK O) c • symG p O hk F l ga (Function.update x (k : ℤ) a) := by
  rw [symG_update p O hk F l ga x k hk', symG_update p O hk F l ga x k hk', map_smul, smul_mul_assoc,
    map_smul, smul_mul_assoc, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    ← MvPolynomial.smul_eq_C_mul]

theorem symG_span (Q : Submodule (KK O) (MvPolynomial (TV n' (m + 1)) (KK O))) (Sj : ℤ → Set (SegRing O r K))
    (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ)
    (h : ∀ x : ℤ → SegRing O r K, (∀ j : ℕ, j < F.J → x j ∈ Sj j) → symG p O hk F l ga x ∈ Q) :
    ∀ x : ℤ → SegRing O r K, (∀ j : ℕ, j < F.J → x j ∈ Submodule.span O (Sj j)) → symG p O hk F l ga x ∈ Q := by
  have key : ∀ k : ℕ, ∀ x : ℤ → SegRing O r K,
      (∀ j : ℕ, j < F.J → (j < k → x j ∈ Submodule.span O (Sj j)) ∧ (k ≤ j → x j ∈ Sj j)) →
        symG p O hk F l ga x ∈ Q := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact h x (fun j hj => (hx j hj).2 (Nat.zero_le j))
    | succ k ih =>
      intro x hx
      by_cases hkJ : k < F.J
      · have hk' : k ∈ Finset.range F.J := Finset.mem_range.2 hkJ
        have hspan : ∀ y ∈ Submodule.span O (Sj k),
            symG p O hk F l ga (Function.update x (k : ℤ) y) ∈ Q := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hyS =>
            apply ih
            intro j hj
            by_cases hjk : j = k
            · rw [hjk, Function.update_self]
              exact ⟨fun h' => absurd h' (lt_irrefl _), fun _ => hyS⟩
            · have hne : (j : ℤ) ≠ (k : ℤ) := by exact_mod_cast hjk
              rw [Function.update_of_ne hne]
              exact ⟨fun h' => (hx j hj).1 (by omega), fun h' => (hx j hj).2 (by omega)⟩
          | zero =>
            rw [symG_zero p O hk F l ga x k hk']
            exact Q.zero_mem
          | add a b _ _ ha hb =>
            rw [symG_add p O hk F l ga x k hk']
            exact Q.add_mem ha hb
          | smul c a _ ha =>
            rw [symG_smul p O hk F l ga x k hk']
            exact Q.smul_mem _ ha
        have h1 := hspan (x k) ((hx k hkJ).1 (Nat.lt_succ_self k))
        rwa [Function.update_eq_self] at h1
      · apply ih
        intro j hj
        exact ⟨fun h' => (hx j hj).1 (by omega), fun h' => absurd h' (by omega)⟩
  intro x hx
  exact key F.J x (fun j hj => ⟨fun _ => hx j hj, fun h' => absurd h' (by omega)⟩)

end Multi

def g2mg (p n' : ℕ) [NeZero n'] (r K : ℕ) (F : Frames n' r) (deg : Fin n' → ℕ) (mS : ℕ) (Y : ℝ) (j x : ℤ) : ℤ :=
  (mS : ℤ) + (⌊(deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) /
    (((r + K : ℕ) : ℝ) ^ 2 * Y)⌋₊ : ℤ)

def g2th (p n' : ℕ) [NeZero n'] {r : ℕ} (F : Frames n' r) (deg : Fin n' → ℕ) (j x : ℤ) : ℝ :=
  (deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) / 2

theorem symbol_spaces_le_pair_span (CLa : ℝ) (p n' : ℕ) [NeZero n'] (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K]
    (F : Frames n' r) (deg : Fin n' → ℕ) (L₁ Ns mS : ℕ) (a Y : ℝ) (j : ℤ) {x : SegRing O r K}
    (hx : x ∈ symbolSpaces CLa p n' O r K F deg L₁ Ns mS a Y j) :
    x ∈ Submodule.span O (pairSet O r K F j (g2mg p n' r K F deg mS Y j) (g2th p n' F deg j)) :=
  (Submodule.mem_inf.1 hx).1

end Formalism.MainNotions.TestSideWords
