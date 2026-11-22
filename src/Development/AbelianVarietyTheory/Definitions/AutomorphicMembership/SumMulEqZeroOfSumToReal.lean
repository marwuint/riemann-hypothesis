import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

section Forms

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁]

def balForms : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | (∀ y z, β y z = β z y) ∧ ∀ (a : O) y z, β (a • y) z = β y (bar a • z)}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    exact ⟨fun y z => by simp only [LinearMap.add_apply, h1 y z, k1 y z],
      fun a y z => by simp only [LinearMap.add_apply, h2 a y z, k2 a y z]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro n β ⟨h1, h2⟩
    exact ⟨fun y z => by simp only [LinearMap.smul_apply, h1 y z],
      fun a y z => by simp only [LinearMap.smul_apply, h2 a y z]⟩

def realForms : Submodule ℝ (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) where
  carrier := {B | (∀ y z, B y z = B z y) ∧ ∀ (a : O) y z, B (a • y) z = B y (bar a • z)}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    exact ⟨fun y z => by simp only [LinearMap.add_apply, h1 y z, k1 y z],
      fun a y z => by simp only [LinearMap.add_apply, h2 a y z, k2 a y z]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro n β ⟨h1, h2⟩
    exact ⟨fun y z => by simp only [LinearMap.smul_apply, h1 y z],
      fun a y z => by simp only [LinearMap.smul_apply, h2 a y z]⟩

variable {bar X}

theorem mem_balForms {β : LinearMap.BilinForm ℤ X} : β ∈ balForms bar X ↔
    (∀ y z, β y z = β z y) ∧ ∀ (a : O) y z, β (a • y) z = β y (bar a • z) := Iff.rfl

theorem mem_realForms {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} : B ∈ realForms bar X ↔
    (∀ y z, B y z = B z y) ∧ ∀ (a : O) y z, B (a • y) z = B y (bar a • z) := Iff.rfl

theorem balForms_eq_levelForms {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] : balForms H.bar X = levelForms H 1 X := by
  ext β
  simp [mem_balForms, mem_levelForms]

theorem mem_balForms_int {X : Type} [AddCommGroup X] {β : LinearMap.BilinForm ℤ X} :
    β ∈ balForms (id : ℤ → ℤ) X ↔ ∀ y z, β y z = β z y :=
  ⟨fun h => h.1, fun h => ⟨h, fun a y z => by simp⟩⟩

def pull (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) : LinearMap.BilinForm ℤ X :=
  β.compl₁₂ r.toAddMonoidHom.toIntLinearMap r.toAddMonoidHom.toIntLinearMap

@[simp] theorem pull_apply (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) (a b : X) : pull r β a b = β (r a) (r b) := rfl

theorem pull_mem (r : X →ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (h : β ∈ balForms bar X₁) : pull r β ∈ balForms bar X :=
  ⟨fun y z => h.1 _ _, fun a y z => by simp only [pull_apply, map_smul, h.2 a]⟩

variable (bar) in

def pullBal (r : X →ₗ[O] X₁) : balForms bar X₁ →ₗ[ℤ] balForms bar X where
  toFun β := ⟨pull r β, pull_mem r β.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (bar) in

def pullBalEquiv (e : X ≃ₗ[O] X₁) : balForms bar X₁ ≃ₗ[ℤ] balForms bar X :=
  LinearEquiv.ofLinear (pullBal bar e.toLinearMap) (pullBal bar e.symm.toLinearMap)
    (by ext β a b; exact congrArg₂ (fun y z => β.1 y z) (e.symm_apply_apply a) (e.symm_apply_apply b))
    (by ext β a b; exact congrArg₂ (fun y z => β.1 y z) (e.apply_symm_apply a) (e.apply_symm_apply b))

def toReal (β : LinearMap.BilinForm ℤ X) : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := β.compr₂ (Algebra.linearMap ℤ ℝ)

@[simp] theorem toReal_apply (β : LinearMap.BilinForm ℤ X) (a b : X) : toReal β a b = (β a b : ℝ) := by simp [toReal]

theorem toReal_mem {β : LinearMap.BilinForm ℤ X} (h : β ∈ balForms bar X) : toReal β ∈ realForms bar X :=
  ⟨fun y z => by simp only [toReal_apply, h.1 y z], fun a y z => by simp only [toReal_apply, h.2 a y z]⟩

theorem sum_mul_eq_zero_of_sum_toReal {L ι : Type} [AddCommGroup L] [Fintype ι] {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X}
    (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {β : ι → L} {c : ι → ℝ} (h : ∑ i, c i • toReal (j (β i)) = 0) :
    ∑ i, c i * (ℓ (β i) : ℝ) = 0 := by
  have key : ∀ (f : Module.Dual ℚ ℝ) (z : ι → ℤ), f (∑ i, c i * (z i : ℝ)) = ∑ i, f (c i) * z i := fun f z => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun f => ?_
  obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) fun i => f (c i)
  choose n hn using hn
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
  have hn' : ∀ z : ι → ℤ, ((∑ i, n i * z i : ℤ) : ℚ) = D * ∑ i, f (c i) * z i := fun z => by
    rw [Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (n i : ℚ) = D * f (c i) := by simpa [Submonoid.smul_def] using hn i
    rw [Int.cast_mul, this, mul_assoc]
  have h0 : ∑ i, n i • β i = 0 := hj (LinearMap.ext₂ fun a b => by
    have h1 : ∑ i, c i * (j (β i) a b : ℝ) = 0 := by simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
    have h2 := hn' fun i => j (β i) a b
    rw [← key, h1, map_zero, mul_zero] at h2
    simpa [LinearMap.sum_apply] using (by exact_mod_cast h2 : ∑ i, n i * j (β i) a b = 0))
  have h3 := hn' fun i => ℓ (β i)
  rw [show ∑ i, n i * ℓ (β i) = 0 by simpa using congrArg ℓ h0] at h3
  rw [key]
  exact (mul_eq_zero.1 (h3.symm.trans Int.cast_zero)).resolve_left hD'

def pullR (r : X →ₗ[O] X₁) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) : X →ₗ[ℤ] X →ₗ[ℤ] ℝ :=
  B.compl₁₂ r.toAddMonoidHom.toIntLinearMap r.toAddMonoidHom.toIntLinearMap

@[simp] theorem pullR_apply (r : X →ₗ[O] X₁) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (a b : X) : pullR r B a b = B (r a) (r b) := rfl

def IsPosDef (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X), LinearIndependent ℤ x → ∀ c : Fin n → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * B (x i) (x j)

theorem IsPosDef.nonneg {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) (y : X) : 0 ≤ B y y := by
  by_cases hy : LinearIndependent ℤ ![y]
  · simpa using (h 1 _ hy ![1] (by simp)).le
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hy
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have h0 : g 0 • y = 0 := by simpa using hg
    have h1 : (g 0 : ℝ) * B y y = 0 := by
      rw [← zsmul_eq_mul, ← map_smul, h0, map_zero]
    exact ((mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hi)).ge

theorem isPosDef_iff_basis {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    IsPosDef B ↔ ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * B (b i) (b j) := by
  constructor
  · intro h c hc
    let e := (Fintype.equivFin ι).symm
    have := h _ (b ∘ e) (b.linearIndependent.comp e e.injective) (c ∘ e) fun h0 => hc (by
      ext i; simpa using congrFun h0 (e.symm i))
    simp only [Function.comp] at this
    rw [← e.sum_comp]
    simpa only [← e.sum_comp (fun j => _ * c j * B _ (b j))] using this
  · intro h n x hx c hc
    have h1 : LinearIndependent ℤ fun i => b.equivFun (x i) := hx.map' b.equivFun.toLinearMap b.equivFun.ker
    have h2 := (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 h1
    have h3 : (fun k => ∑ i, c i * (b.repr (x i) k : ℝ)) ≠ 0 := fun h0 => hc (by
      ext i
      refine Fintype.linearIndependent_iff.1 h2 c ?_ i
      ext k
      simpa using congrFun h0 k)
    refine (h _ h3).trans_eq ?_
    have hx' : ∀ i j, B (x i) (x j) = ∑ k, ∑ l, (b.repr (x i) k : ℝ) * (b.repr (x j) l : ℝ) * B (b k) (b l) := fun i j => by
      conv_lhs => rw [← b.sum_repr (x i), ← b.sum_repr (x j)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp only [hx', Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ l, ∑ i, ∑ j, c i * c j * ((b.repr (x i) k : ℝ) * (b.repr (x j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (x i) k : ℝ) * (b.repr (x j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

variable (bar X) in

def psdCone : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module O X₁) (_ : Module.Projective O X₁) (r : X →ₗ[O] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ B₁ ∈ realForms bar X₁ ∧ IsPosDef B₁ ∧
    ∀ a b, B a b = B₁ (r a) (r b)}

theorem mem_realForms_of_mem_psdCone {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ psdCone bar X) : B ∈ realForms bar X := by
  obtain ⟨X₁, _, _, _, r, B₁, -, h1, -, h2⟩ := h
  exact ⟨fun y z => by rw [h2, h2, h1.1], fun a y z => by rw [h2, h2, r.map_smul, r.map_smul, h1.2]⟩

theorem nonneg_of_mem_psdCone {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ psdCone bar X) (y : X) : 0 ≤ B y y := by
  obtain ⟨X₁, _, _, _, r, B₁, -, -, h1, h2⟩ := h
  exact h2 y y ▸ h1.nonneg _

theorem IsPosDef.mem_psdCone [Module.Projective O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) (hB : B ∈ realForms bar X) :
    B ∈ psdCone bar X := ⟨X, _, _, inferInstance, LinearMap.id, B, Function.surjective_id, hB, h, fun _ _ => rfl⟩

theorem mem_psdCone_of_comp {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ}
    (h : B₁ ∈ psdCone bar X₁) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : ∀ a b, B a b = B₁ (r a) (r b)) : B ∈ psdCone bar X := by
  obtain ⟨X₂, _, _, _, s, B₂, hs, h1, h2, h3⟩ := h
  exact ⟨X₂, _, _, inferInstance, s ∘ₗ r, B₂, hs.comp hr, h1, h2, fun a b => by rw [hB, h3]; rfl⟩

theorem pullR_mem_psdCone {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ}
    (h : B₁ ∈ psdCone bar X₁) : pullR r B₁ ∈ psdCone bar X := mem_psdCone_of_comp hr h fun _ _ => rfl

theorem zero_mem_psdCone : (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ psdCone bar X :=
  ⟨PUnit, _, _, inferInstance, 0, 0, fun _ => ⟨0, rfl⟩, zero_mem _, fun n x hx c hc => by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hc
    exact (hx.ne_zero i rfl).elim, fun _ _ => rfl⟩

theorem smul_mem_psdCone {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ psdCone bar X) {t : ℝ} (ht : 0 ≤ t) : t • B ∈ psdCone bar X := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_smul]; exact zero_mem_psdCone
  obtain ⟨X₁, _, _, _, r, B₁, hr, h1, h2, h3⟩ := h
  refine ⟨X₁, _, _, inferInstance, r, t • B₁, hr, Submodule.smul_mem _ _ h1, fun n x hx c hc => ?_,
    fun a b => by simp [h3]⟩
  refine (mul_pos ht (h2 n x hx c hc)).trans_eq ?_
  simp only [Finset.mul_sum, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Forms

section Part

variable {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {m m' : ℕ}

theorem isPartOfBasis_map {v : Fin m → L} (h : IsPartOfBasis v) (e : L ≃ₗ[ℤ] L') : IsPartOfBasis fun i => e (v i) := by
  obtain ⟨n, b, hb⟩ := h
  exact ⟨n, b.map e, fun i => by simp [hb]⟩

theorem isPartOfBasis_comp {v : Fin m → L} (h : IsPartOfBasis v) (s : Fin m' ↪ Fin m) : IsPartOfBasis fun i => v (s i) := by
  classical
  obtain ⟨n, b, hb⟩ := h
  let f : Fin m' ↪ Fin m ⊕ Fin n := s.trans ⟨Sum.inl, Sum.inl_injective⟩
  let e : Fin m' ⊕ Fin _ ≃ Fin m ⊕ Fin n :=
    ((Equiv.ofInjective f f.injective).sumCongr (Fintype.equivFin _).symm).trans (Equiv.Set.sumCompl (Set.range f))
  exact ⟨_, b.reindex e.symm, fun i => by simp [e, f, hb]⟩

end Part

section Cones

variable {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m m' : ℕ}

def evalR (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ := φ.eval X fun a b => B a b

@[simp] theorem evalR_toReal (β : LinearMap.BilinForm ℤ X) : evalR φ (toReal β) = φ.evalZ β := by
  simp [evalR, InvFun.evalZ]

theorem evalR_pullR {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) :
    evalR φ (pullR r B) = evalR φ B := φ.eval_comp hr fun a b => B a b

theorem evalZ_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    φ.evalZ (pull r β) = φ.evalZ β := φ.eval_comp hr fun a b => (β a b : ℝ)

@[simp] theorem evalR_zero : evalR φ (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) = 0 :=
  (φ.eval_comp (X₁ := PUnit) (r := 0) (fun _ => ⟨0, rfl⟩) fun _ _ => 0).trans (φ.eval_of_subsingleton _)

theorem linearOn_iff (γ : Fin m → LinearMap.BilinForm ℤ X) : φ.LinearOn γ ↔
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → evalR φ (∑ i, c i • toReal (γ i)) = ∑ i, c i * φ.evalZ (γ i) := by
  simp [InvFun.LinearOn, evalR, LinearMap.sum_apply]

variable {φ} in

theorem linearOn_comp {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) (s : Fin m' ↪ Fin m) :
    φ.LinearOn fun i => γ (s i) := by
  intro c hc
  have key : ∀ f : Fin m → ℝ, ∑ j, Function.extend s c 0 j * f j = ∑ i, c i * f (s i) := fun f => by
    symm
    refine Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) fun i => by rw [s.injective.extend_apply]
    rw [Function.extend_apply' _ _ _ hj]; simp
  have := h (Function.extend s c 0) fun j => by
    by_cases hj : ∃ i, s i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [s.injective.extend_apply]; exact hc i
    · rw [Function.extend_apply' _ _ _ hj]; rfl
  simpa only [key] using this

variable {φ} in

theorem linearOn_pull_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁} :
    (φ.LinearOn fun i => pull r (γ i)) ↔ φ.LinearOn γ := by
  refine forall₂_congr fun c _ => ?_
  simp only [evalZ_pull φ hr, pull_apply]
  rw [φ.eval_comp hr fun a b => ∑ i, c i * (γ i a b : ℝ)]

def IsStrict (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ (∀ i, (ℓ (γ i) : ℝ) = N * φ.evalZ (γ i)) ∧
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i

structure IsCone (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop where

  mem : ∀ i, γ i ∈ balForms bar X

  nonneg : ∀ i y, 0 ≤ γ i y y

  basis : IsPartOfBasis fun i => (⟨γ i, mem i⟩ : balForms bar X)

  linear : φ.LinearOn γ

  strict : IsStrict bar φ γ

variable {bar φ}

theorem IsStrict.reindex {γ : Fin m → LinearMap.BilinForm ℤ X} (h : IsStrict bar φ γ) (s : Fin m' ≃ Fin m) :
    IsStrict bar φ fun i => γ (s i) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h
  refine ⟨N, ℓ, hN, fun i => h1 _, h2, fun β hβ hp he => ?_⟩
  obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp he
  exact ⟨k, c ∘ s, hk, hc.trans (s.sum_comp fun i => c i • γ i).symm⟩

theorem IsStrict.of_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsStrict bar φ fun i => pull r (γ i)) : IsStrict bar φ γ := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h
  let P : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
    { toFun := pull r, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨N, ℓ ∘ₗ P, hN, fun i => (h1 i).trans (by rw [evalZ_pull φ hr]), fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← evalZ_pull φ hr]
    exact h2 _ (pull_mem r hβ) fun y => hp _
  · rw [← evalZ_pull φ hr] at he
    obtain ⟨k, c, hk, hc⟩ := h3 _ (pull_mem r hβ) (fun y => hp _) he
    refine ⟨k, c, hk, LinearMap.ext₂ fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hc a b

omit [Module.Finite O X] [Module.Finite O X₁] in

@[simp] theorem pull_symm_pull (e : X ≃ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) :
    pull e.symm.toLinearMap (pull e.toLinearMap β) = β := LinearMap.ext₂ fun a b => by simp

omit [Module.Finite O X] [Module.Finite O X₁] in

@[simp] theorem pull_pull_symm (e : X ≃ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X) :
    pull e.toLinearMap (pull e.symm.toLinearMap β) = β := LinearMap.ext₂ fun a b => by simp

namespace IsCone

variable {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem linearIndependent (h : IsCone bar φ γ) : LinearIndependent ℤ γ :=
  h.basis.linearIndependent.map' (balForms bar X).subtype (Submodule.ker_subtype _)

theorem injective (h : IsCone bar φ γ) : Function.Injective γ := h.linearIndependent.injective

theorem comp (h : IsCone bar φ γ) (s : Fin m' ↪ Fin m) (hs : IsStrict bar φ fun i => γ (s i)) :
    IsCone bar φ fun i => γ (s i) :=
  ⟨fun _ => h.mem _, fun _ => h.nonneg _, isPartOfBasis_comp h.basis s, linearOn_comp h.linear s, hs⟩

theorem reindex (h : IsCone bar φ γ) (s : Fin m' ≃ Fin m) : IsCone bar φ fun i => γ (s i) :=
  h.comp s.toEmbedding (h.strict.reindex s)

theorem pull_equiv {γ : Fin m → LinearMap.BilinForm ℤ X₁} (h : IsCone bar φ γ) (e : X ≃ₗ[O] X₁) :
    IsCone bar φ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, isPartOfBasis_map h.basis (pullBalEquiv bar e),
    (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

theorem evalZ_smul (h : IsCone bar φ γ) (M : ℕ) (i : Fin m) : φ.evalZ ((M : ℤ) • γ i) = M * φ.evalZ (γ i) := by
  have h1 : φ.LinearOn fun _ : Fin 1 => γ i :=
    linearOn_comp h.linear ⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩
  simpa [InvFun.evalZ] using h1 ![M] (by simp)

theorem linearOn_smul (h : IsCone bar φ γ) (M : ℕ) : φ.LinearOn fun i => (M : ℤ) • γ i := by
  intro c hc
  have := h.linear (fun i => c i * M) fun i => mul_nonneg (hc i) M.cast_nonneg
  simp only [h.evalZ_smul]
  simpa [mul_assoc] using this

end IsCone

theorem IsCone.isPartOfBasis_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {φ : InvFun (𝓞 E)}
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h : IsCone H.bar φ γ) {M : ℕ} (hM : M ≠ 0) {δ : Fin m → levelForms H M X}
    (hδ : ∀ i, (δ i : LinearMap.BilinForm ℤ X) = (M : ℤ) • γ i) : IsPartOfBasis δ := by
  let f : balForms H.bar X →ₗ[ℤ] levelForms H M X :=
    ((M : ℤ) • (balForms H.bar X).subtype).codRestrict _ fun β =>
      (mem_levelForms_iff_smul hM).2 ⟨β, balForms_eq_levelForms H X ▸ β.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun β β' e => Subtype.ext (LinearMap.ext₂ fun a b => ?_), fun β => ?_⟩
    · have := LinearMap.congr_fun₂ (congrArg Subtype.val e) a b
      exact mul_left_cancel₀ (show (M : ℤ) ≠ 0 by exact_mod_cast hM) this
    · obtain ⟨β', h1, h2⟩ := (mem_levelForms_iff_smul hM).1 β.2
      exact ⟨⟨β', (balForms_eq_levelForms H X).symm ▸ h1⟩, Subtype.ext h2.symm⟩
  convert isPartOfBasis_map h.basis (LinearEquiv.ofBijective f hf) with i
  exact Subtype.ext (hδ i)

end Cones

section Fan

variable {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m : ℕ}

structure IsPolFanOn : Prop where

  homog : ∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → evalR φ (t • B) = t * evalR φ B

  superadd : ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X, evalR φ B + evalR φ B' ≤ evalR φ (B + B')

  integral : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, φ.evalZ β = n

  pos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < φ.evalZ β

  face : ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m), IsCone bar φ γ →
    IsCone bar φ fun i => γ (s i)

  cover : ∀ B ∈ psdCone bar X, ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCone bar φ γ ∧
    (∀ i, 0 ≤ c i) ∧ B = ∑ i, c i • toReal (γ i)

  finite : ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
    IsCone bar φ γ → ∃ e : X ≃ₗ[O] X, ∀ i, pull e.toLinearMap (γ i) ∈ S

def IsPolFan (bar : O → O) (q : ℕ) (φ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    IsPolFanOn bar φ X

variable (O) {X} in

def NoEquivRays (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∀ (e : X ≃ₗ[O] X) (i j : Fin m), pull e.toLinearMap (γ i) = γ j → i = j

def NoSelfInt (bar : O → O) (q : ℕ) (φ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ γ → NoEquivRays O γ

variable {bar φ X}

theorem IsPolFan.mono {q q' : ℕ} (h : IsPolFan bar q φ) (hq : q' ≤ q) : IsPolFan bar q' φ :=
  fun X _ _ _ _ hX => h X (hX.trans hq)

theorem NoSelfInt.mono {q q' : ℕ} (h : NoSelfInt bar q φ) (hq : q' ≤ q) : NoSelfInt bar q' φ :=
  fun X _ _ _ _ hX => h X (hX.trans hq)

theorem IsPolFanOn.evalZ_nonneg (h : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) : 0 ≤ φ.evalZ β := by
  rcases eq_or_ne β 0 with rfl | h0
  · rw [← evalR_toReal, show toReal (0 : LinearMap.BilinForm ℤ X) = 0 from LinearMap.ext₂ fun _ _ => by simp, evalR_zero]
  · exact (h.pos β hβ hp h0).le

theorem IsPolFanOn.exists_nat (h : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) : ∃ n : ℕ, φ.evalZ β = n := by
  obtain ⟨n, hn⟩ := h.integral β hβ hp
  have : (0 : ℝ) ≤ n := hn ▸ h.evalZ_nonneg hβ hp
  lift n to ℕ using by exact_mod_cast this
  exact ⟨n, by simpa using hn⟩

end Fan

section Fine

variable {X X₁ : Type} [AddCommGroup X] [AddCommGroup X₁] {m m' : ℕ}

def IsFine (N : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∀ y : X, ∃ μ₀ : X, ∀ i μ, γ i (y + N • μ₀) (y + N • μ₀) ≤ γ i (y + N • μ) (y + N • μ)

variable {N : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem IsFine.comp (h : IsFine N γ) (s : Fin m' → Fin m) : IsFine N fun i => γ (s i) :=
  fun y => (h y).imp fun _ h i => h (s i)

def sqForm (l : X →ₗ[ℤ] ℤ) : LinearMap.BilinForm ℤ X := (LinearMap.mul ℤ ℤ).compl₁₂ l l

@[simp] theorem sqForm_apply (l : X →ₗ[ℤ] ℤ) (a b : X) : sqForm l a b = l a * l b := rfl

end Fine

section RankOne

def mulForm : LinearMap.BilinForm ℤ ℤ := LinearMap.mul ℤ ℤ

@[simp] theorem mulForm_apply (a b : ℤ) : mulForm a b = a * b := rfl

end RankOne

end GlobalTheory.PolFan
