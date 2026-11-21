import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.EigRed

theorem mem_smul_of_sum_eigenvectors {O V ι α : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (I : Ideal O) (B : Submodule O V) (T : ι → Module.End O V) (hT : ∀ i, ∀ x ∈ B, T i x ∈ B) (ev : ι → O)
    (s : Finset α) :
    ∀ (y : α → V) (x : V), (∀ a ∈ s, y a = 0 ∨ ∃ e : ι → O, (∀ i, T i (y a) = e i • y a) ∧ ∃ i, IsUnit (ev i - e i)) →
      x = ∑ a ∈ s, y a → x ∈ B → (∀ i, T i x - ev i • x ∈ I • B) → x ∈ I • B := by
  classical
  have hTI : ∀ i, ∀ m ∈ I • B, T i m ∈ I • B := by
    intro i m hm
    refine Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul hr (hT i n hn)
    · rw [map_add]; exact add_mem ha hb
  induction s using Finset.induction_on with
  | empty => intro y x _ hx _ _; simp [hx]
  | insert a s ha ih =>
    intro y x hy hx hxB hev
    rw [Finset.sum_insert ha] at hx
    rcases hy a (Finset.mem_insert_self _ _) with h0 | ⟨e, he, i, hu⟩
    · exact ih y x (fun b hb => hy b (Finset.mem_insert_of_mem hb)) (by simpa [h0] using hx) hxB hev
    · have h1 : T i x - e i • x ∈ I • B := by
        refine ih (fun b => T i (y b) - e i • y b) _ (fun b hb => ?_) ?_ (sub_mem (hT i x hxB) (B.smul_mem _ hxB))
          (fun j => ?_)
        · rcases hy b (Finset.mem_insert_of_mem hb) with h0 | ⟨e', he', hu'⟩
          · left; simp [h0]
          · right
            refine ⟨e', fun j => ?_, hu'⟩
            rw [he' i, ← sub_smul, map_smul, he' j, smul_comm]
        · rw [hx, map_add, smul_add, he i, map_sum, Finset.smul_sum, Finset.sum_sub_distrib]; abel
        · have h2 : T j (T i x - e i • x) - ev j • (T i x - e i • x) =
              (ev i - e i) • (T j x - ev j • x) + (T j (T i x - ev i • x) - ev j • (T i x - ev i • x)) := by
            simp only [map_sub, map_smul]
            module
          rw [h2]
          exact add_mem (Submodule.smul_mem _ _ (hev j))
            (sub_mem (hTI j _ (hev i)) (Submodule.smul_mem _ _ (hev i)))
      have h3 : (ev i - e i) • x ∈ I • B := by
        have : (ev i - e i) • x = (T i x - e i • x) - (T i x - ev i • x) := by module
        rw [this]; exact sub_mem h1 (hev i)
      obtain ⟨u, hu⟩ := hu
      have h4 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h3
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h4

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [← Module.End.mul_apply]
  unfold eG
  rw [← map_mul, Y.eAlg_idem]

theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b) :
    eG Y i j b (T x) = T (eG Y i j b x) := by
  unfold eG
  induction Y.eAlg i b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.lift_of]
    exact LinearMap.congr_fun (h g) x
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

theorem idempotentImage_stable_of_equivariant (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b)
    (hx : x ∈ V0 Y i j b) : T x ∈ V0 Y i j b := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨T y, ?_, eG_comm Y i j b T h y⟩
  simp only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢
  intro u
  have := LinearMap.congr_fun (h u) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy u, map_smul]

end GlobalTheory.EigRed
