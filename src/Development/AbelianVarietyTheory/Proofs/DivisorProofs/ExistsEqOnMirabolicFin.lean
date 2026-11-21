import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.KirFin

theorem mem_of_separates {X : Type} [TopologicalSpace X] [CompactSpace X] (A : Subalgebra ℂ (X → ℂ))
    (hA : ∀ a ∈ A, IsLocallyConstant a) (hs : ∀ x y, x ≠ y → ∃ a ∈ A, a x ≠ a y) {f : X → ℂ}
    (hf : IsLocallyConstant f) : f ∈ A := by
  classical
  have hind : ∀ a ∈ A, ∀ c : ℂ, (fun x => if a x = c then (1 : ℂ) else 0) ∈ A := by
    intro a ha c
    have hfin := (hA a ha).range_finite
    have e : (fun x => if a x = c then (1 : ℂ) else 0) =
        ∏ d ∈ hfin.toFinset.erase c, (c - d)⁻¹ • (a - algebraMap ℂ (X → ℂ) d) := by
      funext x
      simp only [Finset.prod_apply, Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply, smul_eq_mul,
        Algebra.algebraMap_self, RingHom.id_apply]
      split_ifs with h
      · refine (Finset.prod_eq_one fun d hd => ?_).symm
        rw [h]
        exact inv_mul_cancel₀ (sub_ne_zero.2 (Finset.ne_of_mem_erase hd).symm)
      · exact (Finset.prod_eq_zero (i := a x) (by simp [h]) (by simp)).symm
    rw [e]
    exact A.prod_mem fun d _ => A.smul_mem (A.sub_mem ha (A.algebraMap_mem d)) _
  have hcl : ∀ a : X → ℂ, IsLocallyConstant a → IsClopen {p : X × X | a p.1 ≠ a p.2} := fun a ha => by
    have h1 : IsLocallyConstant fun p : X × X => a p.1 - a p.2 :=
      (ha.comp_continuous continuous_fst).sub (ha.comp_continuous continuous_snd)
    convert (h1.isClopen_fiber 0).compl using 1
    ext p
    simp [sub_eq_zero]
  obtain ⟨t, ht⟩ := (hcl f hf).isClosed.isCompact.elim_finite_subcover
    (fun a : A => {p : X × X | a.1 p.1 ≠ a.1 p.2}) (fun a => (hcl _ (hA _ a.2)).isOpen) (by
      intro p hp
      obtain ⟨a, ha, h⟩ := hs p.1 p.2 fun h => hp (by rw [h])
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, h⟩)
  let T : X → (t → ℂ) := fun x a => a.1.1 x
  have hT : ∀ x y, T x = T y → f x = f y := fun x y h => by
    by_contra hne
    obtain ⟨a, ha, h'⟩ := Set.mem_iUnion₂.1 (ht (show (x, y) ∈ _ from hne))
    exact h' (congrFun h ⟨a, ha⟩)
  have hfin : (Set.range T).Finite :=
    (Set.Finite.pi' fun a : t => (hA _ a.1.2).range_finite).subset (by rintro _ ⟨x, rfl⟩ a; exact ⟨x, rfl⟩)
  let v : (t → ℂ) → ℂ := fun c => if h : c ∈ Set.range T then f h.choose else 0
  have e : f = ∑ c ∈ hfin.toFinset, v c • ∏ a : t, fun x => if a.1.1 x = c a then (1 : ℂ) else 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (T x)]
    · have hx : T x ∈ Set.range T := ⟨x, rfl⟩
      simp only [v, dif_pos hx, T, if_true, Finset.prod_const_one, mul_one]
      exact (hT _ _ hx.choose_spec).symm
    · intro c _ hc
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hc
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg (Ne.symm ha)), mul_zero]
    · simp
  rw [e]
  exact A.sum_mem fun c _ => A.smul_mem (A.prod_mem fun a _ => hind _ a.1.2 _) _

variable {F : Type} [NormedField F]

theorem isEmbedding_coe {n : Type} [Fintype n] [DecidableEq n] : IsEmbedding (fun g : GL n F => g.val) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix n n F => A⁻¹) (fun A hA => ?_) fun u => by simp
  refine (continuousAt_matrix_inv A ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero

variable {m : ℕ}

def lr (g : GL (Fin (m + 1)) F) : Fin (m + 1) → F := g.val (Fin.last m)

theorem lr_mul (g h : GL (Fin (m + 1)) F) : lr (g * h) = lr g ᵥ* h.val := rfl

theorem lr_mul_congr {a b : GL (Fin (m + 1)) F} (h : lr a = lr b) (c : GL (Fin (m + 1)) F) :
    lr (a * c) = lr (b * c) := by rw [lr_mul, lr_mul, h]

theorem continuous_lr : Continuous (lr : GL (Fin (m + 1)) F → _) :=
  continuous_pi fun j => Units.continuous_val.matrix_elem (Fin.last m) j

theorem lr_eq_iff {g : GL (Fin (m + 1)) F} :
    lr g = lr 1 ↔ ∀ j, g.val (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
  simp [lr, funext_iff, Matrix.one_apply, eq_comm]

theorem lr_of_mem {u : GL (Fin (m + 1)) F} (hu : u ∈ unipB F (Fin (m + 1))) : lr u = lr 1 := by
  rw [mem_unipB] at hu
  refine lr_eq_iff.2 fun j => ?_
  split_ifs with h
  · rw [h]; exact hu.2 _
  · exact hu.1 _ _ (Fin.lt_last_iff_ne_last.2 h)

def mirM (A : Matrix (Fin m) (Fin m) F) (x : Fin m → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i => Fin.lastCases (x i) (fun j => A i j) j) i

section
variable (A : Matrix (Fin m) (Fin m) F) (x : Fin m → F)
@[simp] theorem mirM_cc (i j : Fin m) : mirM A x i.castSucc j.castSucc = A i j := by simp [mirM]
@[simp] theorem mirM_cl (i : Fin m) : mirM A x i.castSucc (Fin.last m) = x i := by simp [mirM]
@[simp] theorem mirM_lc (j : Fin m) : mirM A x (Fin.last m) j.castSucc = 0 := by simp [mirM]
@[simp] theorem mirM_ll : mirM A x (Fin.last m) (Fin.last m) = 1 := by simp [mirM]
end

theorem mirM_mul (A B : Matrix (Fin m) (Fin m) F) (x y : Fin m → F) :
    mirM A x * mirM B y = mirM (A * B) (A *ᵥ y + x) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct]

theorem mirM_one : mirM (1 : Matrix (Fin m) (Fin m) F) 0 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem continuous_mirM {Y : Type} [TopologicalSpace Y] {A : Y → Matrix (Fin m) (Fin m) F} {x : Y → Fin m → F}
    (hA : Continuous A) (hx : Continuous x) : Continuous fun y => mirM (A y) (x y) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp only [mirM_cc, mirM_cl, mirM_lc, mirM_ll]
  exacts [continuous_const, continuous_const, (continuous_apply _).comp hx, hA.matrix_elem _ _]

def mir (h : GL (Fin m) F) (x : Fin m → F) : GL (Fin (m + 1)) F :=
  ⟨mirM h.val x, mirM (h⁻¹).val (-((h⁻¹).val *ᵥ x)), by
    rw [mirM_mul, mulVec_neg, mulVec_mulVec, Units.mul_inv, one_mulVec, neg_add_cancel, mirM_one], by
    rw [mirM_mul, Units.inv_mul, add_neg_cancel, mirM_one]⟩

@[simp] theorem mir_val (h : GL (Fin m) F) (x : Fin m → F) : (mir h x).val = mirM h.val x := rfl

theorem mir_mul (g h : GL (Fin m) F) (x y : Fin m → F) : mir g x * mir h y = mir (g * h) (g.val *ᵥ y + x) :=
  Units.ext (mirM_mul _ _ _ _)

theorem mir_one : mir (1 : GL (Fin m) F) 0 = 1 := Units.ext mirM_one

theorem mir_eq (h : GL (Fin m) F) (x : Fin m → F) : mir h x = mir 1 x * mir h 0 := by simp [mir_mul]

def cor : GL (Fin m) F →* GL (Fin (m + 1)) F where
  toFun h := mir h 0
  map_one' := mir_one
  map_mul' g h := by simp [mir_mul]

theorem continuous_cor : Continuous (cor : GL (Fin m) F → _) :=
  isEmbedding_coe.continuous_iff.2 (continuous_mirM Units.continuous_val continuous_const)

theorem continuous_col : Continuous fun x : Fin m → F => mir 1 x :=
  isEmbedding_coe.continuous_iff.2 (continuous_mirM continuous_const continuous_id)

theorem lr_mir (h : GL (Fin m) F) (x : Fin m → F) : lr (mir h x) = lr 1 := by
  funext j
  induction j using Fin.lastCases <;> simp [lr, Matrix.one_apply, (Fin.castSucc_ne_last _).symm]

theorem eq_mirabolicMatrix_of_lastRow_eq {p : GL (Fin (m + 1)) F} (hp : lr p = lr 1) :
    p.val = mirM (p.val.submatrix Fin.castSucc Fin.castSucc) fun i => p.val i.castSucc (Fin.last m) := by
  rw [lr_eq_iff] at hp
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [hp, Fin.castSucc_ne_last]

theorem exists_mir {p : GL (Fin (m + 1)) F} (hp : lr p = lr 1) : ∃ h x, p = mir h x := by
  have hq : lr p⁻¹ = lr 1 := by
    have := lr_mul_congr hp p⁻¹
    rw [mul_inv_cancel, one_mul] at this
    exact this.symm
  have h1 : p.val.submatrix Fin.castSucc Fin.castSucc * (p⁻¹).val.submatrix Fin.castSucc Fin.castSucc = 1 := by
    have h2 := p.mul_inv
    rw [eq_mirabolicMatrix_of_lastRow_eq hp, eq_mirabolicMatrix_of_lastRow_eq hq, mirM_mul] at h2
    ext i j
    have := congrFun (congrFun h2 i.castSucc) j.castSucc
    rw [mirM_cc] at this
    rw [this]
    simp [Matrix.one_apply]
  exact ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, _, Units.ext (eq_mirabolicMatrix_of_lastRow_eq hp)⟩

theorem mir_mem_iff {u : GL (Fin m) F} {x : Fin m → F} : mir u x ∈ unipB F (Fin (m + 1)) ↔ u ∈ unipB F (Fin m) := by
  rw [mem_unipB, mem_unipB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j h => by simpa using h1 i.castSucc j.castSucc (by simpa using h), fun i => by simpa using h2 i.castSucc⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (not_lt.2 (Fin.le_last _))
      · simpa using h1 _ _ (by simpa using hij)
    · induction i using Fin.lastCases <;> simp [h2]

theorem superDiag_mir (u : GL (Fin (m + 1)) F) (x : Fin (m + 1) → F) :
    superDiag (mir u x) = superDiag u + x (Fin.last m) := by
  unfold superDiag
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc (n := m + 1), mir_val, mirM_cc, mirM_cl, mirM_lc, mirM_ll, Fin.val_castSucc,
    Fin.val_last, Finset.sum_add_distrib]
  have : ∀ i : Fin (m + 1), (m = i.val) ↔ i = Fin.last m := fun i => by simp [Fin.ext_iff, eq_comm]
  simp [this]

theorem superDiag_one' : superDiag (1 : GL (Fin m) F) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact Matrix.one_apply_ne fun h => by simp [h] at hj

theorem isCompact_blocks {C : Set (GL (Fin (m + 1)) F)} (hC : IsCompact C) :
    IsCompact {h : GL (Fin m) F | ∃ x, mir h x ∈ C} := by
  rw [isEmbedding_coe.isInducing.isCompact_iff]
  have h1 : IsCompact (C ∩ {p | lr p = lr 1}) := hC.inter_right (isClosed_eq continuous_lr continuous_const)
  convert h1.image (f := fun p : GL (Fin (m + 1)) F => p.val.submatrix Fin.castSucc Fin.castSucc)
    (Units.continuous_val.matrix_submatrix _ _) using 1
  ext A
  constructor
  · rintro ⟨h, ⟨x, hx⟩, rfl⟩
    exact ⟨mir h x, ⟨hx, lr_mir h x⟩, by ext i j; simp⟩
  · rintro ⟨p, ⟨hp, hp'⟩, rfl⟩
    obtain ⟨h, x, rfl⟩ := exists_mir hp'
    exact ⟨h, ⟨x, hp⟩, by ext i j; simp⟩

def Eqv (ψ : AddChar F ℂ) {n : ℕ} (W : GL (Fin n) F → ℂ) : Prop :=
  ∀ u ∈ unipB F (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g

theorem Eqv.apply_mir {ψ : AddChar F ℂ} {W : GL (Fin (m + 2)) F → ℂ} (h : Eqv ψ W) (g : GL (Fin (m + 1)) F)
    (x : Fin (m + 1) → F) : W (mir g x) = ψ (x (Fin.last m)) * W (cor g) := by
  rw [mir_eq, h _ (mir_mem_iff.2 (one_mem _)), superDiag_mir, superDiag_one', zero_add]
  rfl

theorem Eqv.res {ψ : AddChar F ℂ} {W : GL (Fin (m + 2)) F → ℂ} (h : Eqv ψ W) :
    Eqv ψ fun x : GL (Fin (m + 1)) F => W (cor x) := fun u hu g => by
  simp only [map_mul]
  rw [h (cor u) (mir_mem_iff.2 hu)]
  change ψ (superDiag (mir u 0)) * _ = _
  rw [superDiag_mir, Pi.zero_apply, add_zero]

end GlobalTheory.JSW.KirFin
