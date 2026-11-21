import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem inN_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) : g.val.BlockTriangular (lev p) := by
  intro r s h
  rw [hg r s h.le, Matrix.one_apply_ne]
  rintro rfl; exact lt_irrefl _ h

theorem mul_entry {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (r s) (hrs : lev p s ≤ lev p r) : (g.val * h) r s = h r s := by
  have : (g.val * h) r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * h) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : lev p t ≤ lev p r
    · rw [hg r t ht]
    · rw [hh (show lev p s < lev p t by omega)]; simp
  rw [this, Matrix.one_mul]

def Nsub (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | InN p g}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    rw [Units.val_mul, mul_entry ha (inN_tri hb) r s hrs, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have h1 : (a⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular (inN_tri ha)
    rw [← mul_entry ha h1 r s hrs, Units.mul_inv]

theorem mem_N_iff {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ N k n c p ↔ InN p g := by
  have : N k n c p = Nsub k n c p := Subgroup.closure_eq (Nsub k n c p)
  rw [this]; rfl

theorem conj_mem {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ N k n c p := by
  rw [mem_N_iff] at hu ⊢
  rw [← map_inv]
  have h11 : u.val.toBlocks₁₁ = 1 := by
    ext r s
    have := hu (Sum.inl r) (Sum.inl s) le_rfl
    simpa [Matrix.one_apply, toBlocks₁₁] using this
  have hv : ((embX c g⁻¹) * u * embX c g).val = fromBlocks 1 ((g⁻¹).val * u.val.toBlocks₁₂)
      (u.val.toBlocks₂₁ * g.val) u.val.toBlocks₂₂ := by
    rw [Units.val_mul, Units.val_mul, ← fromBlocks_toBlocks u.val, h11]
    simp [embX, fromBlocks_multiply]
  rintro (r | r) (s | s) h <;> rw [hv]
  · simp [Matrix.one_apply]
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [Matrix.mul_apply, toBlocks₁₂, this]
  · have : ∀ t, u.val (Sum.inr r) (Sum.inl t) = 0 := fun t => by
      simpa using hu (Sum.inr r) (Sum.inl t) h
    simp [Matrix.mul_apply, toBlocks₂₁, this]
  · simpa [toBlocks₂₂] using hu (Sum.inr r) (Sum.inr s) h

def mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s => if h : lev p r < lev p s then e ⟨(r, s), h⟩ else (1 : Matrix _ _ k) r s

theorem det_mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    (mkN p e).det = 1 := by
  have ht : (mkN p e).BlockTriangular (lev p) := by
    intro r s h
    have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, not_lt.2 h.le, this]
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (mkN p e).toSquareBlock (lev p) a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, mkN, hr, hs, Matrix.one_apply]
  rw [this, det_one]

def mkNel (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) : N k n c p :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (mkN p e) (by rw [det_mkN]; exact one_ne_zero), by
    rw [mem_N_iff]
    intro r s h
    show mkN p e r s = _
    simp [mkN, not_lt.2 h]⟩

section meas
variable [MeasurableSpace k]

theorem coord_embedding (p : ℕ) : MeasurableEmbedding
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) ∧ Function.Surjective
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
  have hs : Function.Surjective
      (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
    intro e
    refine ⟨mkNel p e, ?_⟩
    funext rs
    show mkN p e _ _ = _
    simp [mkN, rs.2]
  refine ⟨MeasurableEmbedding.of_measurable_inverse (g := mkNel (k := k) p) ?_ ?_ ?_ ?_, hs⟩
  · refine measurable_pi_lambda _ fun rs => ?_
    have h1 : Measurable (fun g : GL (n ⊕ Fin c) k => g.val) := comap_measurable _
    have h2 : Measurable (fun m : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => m rs.1.1 rs.1.2) :=
      (measurable_pi_apply rs.1.2).comp (measurable_pi_apply rs.1.1)
    exact h2.comp (h1.comp measurable_subtype_coe)
  · rw [hs.range_eq]; exact MeasurableSet.univ
  · refine Measurable.subtype_mk ?_
    refine measurable_comap_iff.2 ?_
    refine measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun s => ?_
    show Measurable fun e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k => mkN (k := k) p e r s
    by_cases h : lev p r < lev p s
    · simp only [mkN, Matrix.of_apply, dif_pos h]; exact measurable_pi_apply _
    · simp only [mkN, Matrix.of_apply, dif_neg h]; exact measurable_const
  · intro g
    ext r s
    show mkN (k := k) p (fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) r s = _
    by_cases h : lev p r < lev p s
    · simp [mkN, h]
    · simp only [mkN, Matrix.of_apply, dif_neg h]
      exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm

end meas

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def chi (ψ : AddChar k Circle) (p : ℕ) (h : GL (n ⊕ Fin c) k) : ℂ :=
  if h ∈ N k n c p then (ψ (simpleSum h) : ℂ) else 0

def reg (G : Type*) [Group G] : Representation ℂ G (G →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (g * ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

end GlobalTheory.RootEx.Model
