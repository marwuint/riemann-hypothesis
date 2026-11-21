import Mathlib

open scoped NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

noncomputable section Defs

variable {C : Type} [Field C] (w : Valuation C ℝ≥0)

noncomputable def addVal (ℓ c : C) : ℝ := Real.log (w c : ℝ) / Real.log (w ℓ : ℝ)

def HasVal (ℓ c : C) (y : ℝ) : Prop := c ≠ 0 ∧ addVal w ℓ c = y

def IsLatticeBasis {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (x : Fin n → W)
    (X : Submodule w.valuationSubring W) : Prop :=
  LinearIndependent C x ∧ Submodule.span w.valuationSubring (Set.range x) = X

def DetRel (ℓ : C) {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (X : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) : Prop :=
  ∃ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C)
    (m : Fin q → Fin (p + q) → C) (c : C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w (fun i => F.mkQ (u i)) L ∧ IsLatticeBasis w m M ∧
      (∀ i, m i ∈ F) ∧ HasVal w ℓ c y ∧
      (Matrix.of x).det = c * (Matrix.of (Fin.append u m)).det

variable {w}

def eigenSub {S : Type} [DecidableEq S] {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.comap (LinearMap.single w.valuationSubring W τ)

def eigenQuot {S : Type} {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.map (LinearMap.proj τ)

def freeLattice {S : Type} (a : S → w.valuationSubring) (r : ℕ) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {x | ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
    x s i = ((f.eval (a s) : w.valuationSubring) : C)}
  zero_mem' := fun _ => ⟨0, fun _ => by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨f, hf⟩ := hx i
    obtain ⟨g, hg⟩ := hy i
    exact ⟨f + g, fun s => by simp [hf s, hg s]⟩
  smul_mem' := by
    intro c x hx i
    obtain ⟨f, hf⟩ := hx i
    exact ⟨Polynomial.C c * f, fun s => by simp [hf s, Algebra.smul_def]⟩

def unif {S : Type} {r : ℕ} (a : S → w.valuationSubring) (x : S → Fin r → C) :
    S → Fin r → C := fun s => (a s : C) • x s

def filSpace {S : Type} {r : ℕ} (Fil : Submodule w.valuationSubring (S → Fin r → C)) (s : S) :
    Submodule C (Fin r → C) :=
  Submodule.span C (eigenQuot (W := fun _ => Fin r → C) Fil s : Set (Fin r → C))

def quotMap {r : ℕ} (F : Submodule C (Fin r → C)) :
    (Fin r → C) →ₗ[w.valuationSubring] ((Fin r → C) ⧸ F) :=
  F.mkQ.restrictScalars w.valuationSubring

def lie {S : Type} {r : ℕ} (H Fil : Submodule w.valuationSubring (S → Fin r → C)) :
    Submodule w.valuationSubring (∀ s, (Fin r → C) ⧸ filSpace Fil s) :=
  H.map (LinearMap.pi fun s => quotMap (filSpace Fil s) ∘ₗ LinearMap.proj s)

structure IsFiltration {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  le : Fil ≤ freeLattice a r
  stable : ∀ x ∈ Fil, unif a x ∈ Fil
  saturated : ∀ x ∈ freeLattice a r, ∀ c : w.valuationSubring, c ≠ 0 → c • x ∈ Fil → x ∈ Fil

def diffGen {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (τ : S) :
    w.valuationSubring := ∏ s ∈ Finset.univ.erase τ, (a τ - a s)

def flatLattice {S : Type} {r : ℕ} (a : S → w.valuationSubring) (τ : S)
    (d : w.valuationSubring) : Submodule w.valuationSubring (Fin r → C) :=
  (eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ).map
    (LinearMap.lsmul w.valuationSubring (Fin r → C) d)

end Defs

noncomputable section Example

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

def resPair (a : Bool → w.valuationSubring) (r : ℕ) :
    (Bool → Fin r → C) →ₗ[C] (Bool → Fin r → C) →ₗ[C] C :=
  LinearMap.mk₂ C
    (fun x y => ∑ i, (x true i * y true i - x false i * y false i) / ((a true : C) - a false))
    (fun x x' y => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem resPair_apply (a : Bool → w.valuationSubring) (r : ℕ) (x y : Bool → Fin r → C) :
    resPair a r x y =
      ∑ i, (x true i * y true i - x false i * y false i) / ((a true : C) - a false) := rfl

end Example

end GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference
