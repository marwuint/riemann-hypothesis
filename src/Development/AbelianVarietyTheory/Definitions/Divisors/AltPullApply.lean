import Mathlib

noncomputable section

namespace GlobalTheory.KS

variable {O : Type} [Ring O] {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

def matAct (ρ : O →+* Module.End R V) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : (Fin m → V) →ₗ[R] (Fin m → V) :=
  LinearMap.pi fun i => ∑ j, ρ (M i j) ∘ₗ LinearMap.proj j

abbrev Alt (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] (E : Type) [CommRing E] [Algebra R E] (q : ℕ) :
    Type := W [⋀^Fin q]→ₗ[R] E

variable {E : Type} [CommRing E] [Algebra R E]

def altPull (E : Type) [CommRing E] [Algebra R E] {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) : Alt R W E q →ₗ[E] Alt R W' E q where
  toFun f := f.compLinearMap u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem altPull_apply {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) (f : Alt R W E q) (x : Fin q → W') : altPull E u q f x = f fun i => u (x i) := rfl

def altOp (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (q : ℕ) :
    Module.End E (Alt R (Fin m → V) E q) :=
  ε.sum fun M c => c • altPull E (matAct ρ M) q

structure IsCut (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) : Prop where
  idem : altOp ρ ε k * altOp ρ ε k = altOp ρ ε k
  zero : ∀ q, q ≠ k → altOp ρ ε q = 0

variable {Γ : Type} [Group Γ]

end GlobalTheory.KS
