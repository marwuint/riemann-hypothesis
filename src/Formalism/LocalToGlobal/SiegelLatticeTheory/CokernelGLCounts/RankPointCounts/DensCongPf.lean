import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel

section Act

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι]

def act (A : Matrix ι ι E) (v : ι → V) : ι → V := fun b => ∑ a, A a b • v a

theorem act_act (A B : Matrix ι ι E) (v : ι → V) : act A (act B v) = act (B * A) v := by
  funext b
  simp only [act, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem h_sum_left {κ : Type} (s : Finset κ) (f : κ → V) (y : V) : H.h (∑ c ∈ s, f c) y = ∑ c ∈ s, H.h (f c) y := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact H.h_zero_left y
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, H.h_add_left, ih]

theorem h_right (x y : V) : H.h x y = M.L.cj (H.h y x) := by
  rw [H.h_herm x y, M.L.cj_cj]

theorem h_sum_right {κ : Type} (s : Finset κ) (f : κ → V) (x : V) : H.h x (∑ c ∈ s, f c) = ∑ c ∈ s, H.h x (f c) := by
  rw [h_right, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun c _ => (h_right H x (f c)).symm

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [h_right, H.h_smul_left, map_mul, ← h_right]

theorem gram_act (A : Matrix ι ι E) (v : ι → V) (a b : ι) :
    H.h (act A v b) (act A v a) =
      ((A.map M.L.cj).transpose * Matrix.of (fun c d => H.h (v d) (v c)) * A) a b := by
  simp only [act, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  rw [h_sum_left]
  simp only [H.h_smul_left, h_sum_right, h_smul_right, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Act

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem act_one (v : ι → V) : act (1 : Matrix ι ι E) v = v := by
  funext b
  simp only [act, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem o_mul_mem (S : Submodule M.L.O E) {o x : E} (ho : o ∈ M.L.O) (hx : x ∈ S) : o * x ∈ S :=
  S.smul_mem ⟨o, ho⟩ hx

theorem cong_act (S : Submodule M.L.O E) (A G : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a b, H.h (v b) (v a) - G a b ∈ S) :
    ∀ a b, H.h (act A v b) (act A v a) - ((A.map M.L.cj).transpose * G * A) a b ∈ S := by
  intro a b
  rw [gram_act, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply]
  refine S.sum_mem fun c _ => ?_
  rw [Finset.sum_mul]
  refine S.sum_mem fun d _ => ?_
  rw [mul_comm _ (A c b), ← mul_assoc]
  rw [mul_comm (A c b)]
  refine o_mul_mem S (Subring.mul_mem _ (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (hAO d a)) (hAO c b)) (hv d c)

theorem mem_lam_act (abelian₂ : Submodule M.L.O V) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a, v a ∈ abelian₂) (b : ι) : act A v b ∈ abelian₂ :=
  abelian₂.sum_mem fun a _ => abelian₂.smul_mem ⟨A a b, hAO a b⟩ (hv a)

theorem mem_span_act (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span M.L.O (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (⟨A a b, hAO a b⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)

theorem mem_spanE_act (A : Matrix ι ι E) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (A a b) (Submodule.subset_span ⟨a, rfl⟩)

theorem prim_act (abelian₂ : Submodule M.L.O V) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (hBA : B * A = 1) (v : ι → V) (hv : H.Prim abelian₂ v) :
    H.Prim abelian₂ (act A v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hback : act B (act A v) = v := by rw [act_act, hAB, act_one]
  refine ⟨mem_lam_act abelian₂ A hAO v h1, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at h2 ⊢
    intro g hg
    have e : ∑ b, g b • act A v b = ∑ a, (A *ᵥ g) a • v a := by
      simp only [act, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
    rw [e] at hg
    have h0 := h2 _ hg
    have hAg : A *ᵥ g = 0 := funext h0
    have : g = B *ᵥ (A *ᵥ g) := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    intro b
    rw [this, hAg, Matrix.mulVec_zero]
    rfl
  · intro x hx hxs
    have hxv : x ∈ Submodule.span E (Set.range v) := by
      refine Submodule.span_le.2 ?_ hxs
      rintro _ ⟨b, rfl⟩
      exact mem_spanE_act A v b
    have hO := h3 x hx hxv
    refine Submodule.span_le.2 ?_ hO
    rintro _ ⟨a, rfl⟩
    have : v a = act B (act A v) a := by rw [hback]
    rw [SetLike.mem_coe, this]
    exact mem_span_act B hBO (act A v) a

end Main

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Count

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : A.det ∈ M.L.O := by
  rw [Matrix.det_apply]
  exact M.L.O.sum_mem fun σ _ => Subring.zsmul_mem _ (M.L.O.prod_mem fun i _ => hA _ _) _

theorem adj_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : ∀ i j, A.adjugate i j ∈ M.L.O := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det_mem _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem]
  · exact hA a b

def cls (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (G₀ : Matrix ι ι E) :
    Set (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) abelian₂) :=
  Set.range fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
    fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)

def psi (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (x : ι → V ⧸ H.smulLat c abelian₂) : ι → V ⧸ H.smulLat c abelian₂ :=
  fun b => ∑ a, (⟨A a b, hAO a b⟩ : M.L.O) • x a

theorem psi_mk (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) :
    psi H abelian₂ c A hAO (fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (v a)) =
      fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act A v a) := by
  funext b
  simp only [psi, act]
  rw [show (Submodule.Quotient.mk (∑ a, A a b • v a) : V ⧸ H.smulLat c abelian₂) =
    (H.smulLat c abelian₂).mkQ (∑ a, A a b • v a) from rfl, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show _ = (H.smulLat c abelian₂).mkQ ((⟨A a b, hAO a b⟩ : M.L.O) • v a)
  rw [LinearMap.map_smul]
  rfl

theorem psi_psi (abelian₂ : Submodule M.L.O V) (c : E) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (x : ι → V ⧸ H.smulLat c abelian₂) :
    psi H abelian₂ c B hBO (psi H abelian₂ c A hAO x) = x := by
  funext b
  simp only [psi, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ a, ∑ y, ((⟨B y b, hBO y b⟩ : M.L.O) * ⟨A a y, hAO a y⟩) • x a =
      (if a = b then (1 : M.L.O) else 0) • x a := by
    intro a
    rw [← Finset.sum_smul]
    congr 1
    apply Subtype.ext
    have h := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at h
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [Finset.sum_congr rfl (fun y _ => mul_comm (B y b) (A a y)), h, Matrix.one_apply]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp

end Count

end Formalism.L2.SG.Pf.DensCongPf
