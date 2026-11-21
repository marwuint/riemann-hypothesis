import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

abbrev Io (S σ : Type) [CommRing S] : Ideal (MvPolynomial σ S) := idealOfVars σ S

def xs (S : Type) [CommRing S] {n : ℕ} (d : ℕ) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => X (k, i)

def lin {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => ∑ l, C (A i l) * X (k, l)

def ev2 {τ : Type} (h : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) : MvPolynomial τ S :=
  aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h

lemma eval_pair_one {τ : Type} (u v : Fin d → MvPolynomial τ S) : ev2 (1 : MvPolynomial (Fin 2 × Fin d) S) u v = 1 := by
  simp [ev2]

lemma eval_pair_sub {τ : Type} (h h' : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) :
    ev2 (h - h') u v = ev2 h u v - ev2 h' u v := by
  simp [ev2]

section Sub

variable {σ τ : Type}

lemma aeval_mem_pow (g : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (k : ℕ) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ k) : aeval g p ∈ Io S τ ^ k := by
  have h1 : Io S σ ≤ (Io S τ).comap (aeval g) := by
    show Ideal.span (Set.range X) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hg i
  exact (Ideal.le_comap_pow (f := aeval g) k) (Ideal.pow_right_mono h1 k hp)

lemma sub_C_mem (p : MvPolynomial σ S) : p - C (coeff 0 p) ∈ Io S σ := by
  have h := (mem_pow_idealOfVars_iff' (σ := σ) (R := S) 1 (p - C (coeff 0 p))).2 (fun x hx => by
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    subst hx0
    simp)
  simpa using h

lemma aeval_sub_aeval_mem (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (p : MvPolynomial σ S) : aeval g p - aeval g' p ∈ Io S τ := by
  have h0 : p - C (coeff 0 p) ∈ Io S σ ^ 1 := by simpa using sub_C_mem p
  have h1 := aeval_mem_pow g hg 1 h0
  have h2 := aeval_mem_pow g' hg' 1 h0
  have h3 := sub_mem (by simpa using h1) (by simpa using h2)
  simpa [map_sub, aeval_C] using h3

lemma aeval_sub_mem_sq (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) {p : MvPolynomial σ S} (hp : p ∈ Io S σ) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  have hp' : p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ S)) := hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa using hgg i
  | zero => simp
  | add x y _ _ hx hy =>
    have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
      simp only [map_add]; ring
    rw [e]; exact add_mem hx hy
  | smul r x hxm hx =>
    have e : aeval g (r • x) - aeval g' (r • x) =
        (aeval g r - aeval g' r) * aeval g x + aeval g' r * (aeval g x - aeval g' x) := by
      simp only [smul_eq_mul, map_mul]; ring
    rw [e]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hx)
    rw [pow_two]
    have hx1 : x ∈ Io S σ ^ 1 := by simpa using hxm
    exact Ideal.mul_mem_mul (aeval_sub_aeval_mem g g' hg hg' r) (by simpa using aeval_mem_pow g hg 1 hx1)

lemma aeval_sub_mem_pow (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) : ∀ (k : ℕ) (p : MvPolynomial σ S), p ∈ Io S σ ^ k →
    aeval g p - aeval g' p ∈ Io S τ ^ (k + 1)
  | 0, p, _ => by simpa using aeval_sub_aeval_mem g g' hg hg' p
  | k + 1, p, hp => by
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun p => aeval g p - aeval g' p ∈ Io S τ ^ (k + 1 + 1)) hp ?_ ?_
    · intro a ha b hb
      have e : aeval g (a * b) - aeval g' (a * b) =
          (aeval g a - aeval g' a) * aeval g b + aeval g' a * (aeval g b - aeval g' b) := by
        simp only [map_mul]; ring
      rw [e]
      refine add_mem ?_ ?_
      · rw [pow_succ]
        have hb1 : b ∈ Io S σ ^ 1 := by simpa using hb
        exact Ideal.mul_mem_mul (aeval_sub_mem_pow g g' hg hg' hgg k a ha)
          (by simpa using aeval_mem_pow g hg 1 hb1)
      · have e2 : Io S τ ^ (k + 1 + 1) = Io S τ ^ k * Io S τ ^ 2 := by rw [← pow_add]
        rw [e2]
        exact Ideal.mul_mem_mul (aeval_mem_pow g' hg' k ha) (aeval_sub_mem_sq g g' hg hg' hgg hb)
    · intro x y hx hy
      have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
        simp only [map_add]; ring
      rw [e]; exact add_mem hx hy

lemma eq_zero_of_isHomogeneous {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j)
    (hm : h ∈ Io S σ ^ (j + 1)) : h = 0 := by
  ext e
  rw [coeff_zero]
  by_contra hne
  have h1 := (mem_pow_idealOfVars_iff (j + 1) h).1 hm e (mem_support_iff.2 hne)
  have h2 : e.degree = j := by
    have := hh hne
    rw [Finsupp.degree_eq_weight_one]
    exact this
  omega

lemma sub_homogeneousComponent_mem {W : MvPolynomial σ S} {j : ℕ} (hW : W ∈ Io S σ ^ j) :
    W - homogeneousComponent j W ∈ Io S σ ^ (j + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hW ⊢
  intro x hx
  rw [coeff_sub, coeff_homogeneousComponent]
  split_ifs with h
  · simp
  · have : x.degree < j := by omega
    simp [hW x this]

end Sub

lemma eval_pair_homogeneous {τ : Type} {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j)
    (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (ev2 h u v).IsHomogeneous j := by
  have := hh.aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) (n := 1)
    (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
  rw [one_mul] at this
  exact this

lemma xs_hom {n : ℕ} (k : Fin n) (i : Fin d) : (xs S d k i).IsHomogeneous 1 := isHomogeneous_X S _

lemma lin_hom {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : (lin A k i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X S _).C_mul _

lemma xs_mem {n : ℕ} (k : Fin n) (i : Fin d) : xs S d k i ∈ Io S (Fin n × Fin d) :=
  Ideal.subset_span ⟨_, rfl⟩

lemma lin_mem {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : lin A k i ∈ Io S (Fin n × Fin d) :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
