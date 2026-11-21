import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open ReciprocityTheory.ChartRestriction.DS Matrix

namespace GlobalTheory.Kg

section Abs

variable {R : Type} [Field R] [Algebra R ℂ] {P M : Type} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module ℂ M]
  [Module R M] [IsScalarTower R ℂ M]

def gdR (L : P →ₗ[R] Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[R] M) : P [⋀^Fin (q + 1)]→ₗ[R] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L X).restrictScalars R).compAlternatingMap f
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L X Y) (f v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c X) (f v) }

structure IsPos (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (N : Submodule ℂ M) : Prop where
  herm : ∀ x y, H y x = starRingEnd ℂ (H x y)
  nonneg : ∀ x ∈ N, 0 ≤ (H x x).re
  definite : ∀ x ∈ N, H x x = 0 → x = 0

end Abs

theorem gd_eq_gdR {P M : Type} [AddCommGroup P] [Module ℝ P] [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] (L : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) :
    GlobalTheory.BorelCoh.gd L f = gdR L f := rfl

section Unitary

variable {T : Type} [Fintype T] [DecidableEq T] {n : ℕ}

def pC (ε : T → Fin n → Bool) : Submodule ℂ (T → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ τ a b, ε τ a = ε τ b → X τ a b = 0}
  add_mem' {X Y} hX hY τ a b h := by simp [hX τ a b h, hY τ a b h]
  zero_mem' τ a b _ := rfl
  smul_mem' c X hX τ a b h := by simp [hX τ a b h]

abbrev NC (ε : T → Fin n → Bool) : Type := {x : T × Fin n × Fin n // ε x.1 x.2.1 ≠ ε x.1 x.2.2}

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def actP (ε : T → Fin n → Bool) (E : T → Fin n → Fin n → Module.End ℂ W) : pC ε →ₗ[ℂ] Module.End ℂ W where
  toFun X := ∑ τ, actM (E τ) (X.1 τ)
  map_add' X Y := by simp [actM, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [actM, Finset.smul_sum, smul_smul]

def trOp {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ W) (x : NC ε) : Module.End ℂ W :=
  E x.1.1 x.1.2.2 x.1.2.1

variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}

def onEach (d : ℕ) (A : Module.End ℂ M) : Module.End ℂ (Fin d → M) := A.compLeft (Fin d)

def onIdx (M : Type) [AddCommGroup M] [Module ℂ M] (x : Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (Fin d → M) :=
  LinearMap.pi fun i => ∑ j, x i j • LinearMap.proj j

def famA (d : ℕ) (E : T → Fin n → Fin n → Module.End ℂ M) : T → Fin n → Fin n → Module.End ℂ (Fin d → M) :=
  fun τ a b => onEach d (E τ a b)

def famB (M : Type) [AddCommGroup M] [Module ℂ M] (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) :
    T → Fin n → Fin n → Module.End ℂ (Fin d → M) := fun τ a b => onIdx M (ξ τ a b)

def codOp {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ M)
    (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (x : NC ε) : Module.End ℂ (Fin d → M) :=
  trOp (famB M ξ) x - trOp (famA d E) x

theorem codOp_eq {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ M)
    (ξ : T → Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) :
    codOp (ε := ε) E ξ = fun x => trOp (famB M ξ) x - trOp (famA d E) x := rfl

theorem trOp_apply {ε : T → Fin n → Bool} (E : T → Fin n → Fin n → Module.End ℂ M) (x : NC ε) :
    trOp E x = E x.1.1 x.1.2.2 x.1.2.1 := rfl

end Unitary

end GlobalTheory.Kg

end
