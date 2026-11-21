import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Jx10

theorem pull {α X : Type} [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ)
    (h : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun x y => k (η x) (η y)) := by
  unfold Formalism.FourierDecayAlt.A5.IsPSD at h ⊢
  intro a
  show (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).im = 0 ∧
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).re
  set b : X → ℂ := fun u => ∑ z ∈ F.filter (fun z => η z = u), a z with hb
  have hmaps : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have rhs : ∀ u v, b u * conj (b v) * k u v =
      ∑ x ∈ F.filter (fun z => η z = u), ∑ y ∈ F.filter (fun z => η z = v),
        a x * conj (a y) * k (η x) (η y) := by
    intro u v
    simp only [hb]
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h1 := (Finset.mem_filter.mp hx).2
    have h2 := (Finset.mem_filter.mp hy).2
    rw [h1, h2] <;> ring
  have key : (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)) =
      ∑ u ∈ F.image η, ∑ v ∈ F.image η, b u * conj (b v) * k u v := by
    simp_rw [rhs]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  rw [key]
  exact h b

theorem inter_of_module (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E)
    (hL : ∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
      algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) (t : E)
    (h : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L) : t ∈ L := by
  by_contra ht
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at ha ⊢
        exact hL c _ ha }
  have hI : I ≠ ⊤ := by
    intro hI
    apply ht
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := by
      rw [hI]
      exact Submodule.mem_top
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E 1 * t ∈ L := h1
    simpa using h2
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨a, haP, haL⟩ := h P hP
  exact haP (hIP haL)

end Formalism.FourierDecayAlt.P.Jx10

namespace Formalism.FourierDecayAlt.P

open Classical in

theorem local_kernel_psd : Formalism.FourierDecayAlt.J.LocalKernelPSD := by
  intro hag hgram K _ _ _ R ψ hLD α η Y
  rw [(hag α Y _).1, ← (hag α Y _).2]
  exact Jx10.pull η Y (A5.Kp R ψ) (hgram K R ψ hLD (Y.image η))

theorem intersection_of_local : Formalism.FourierDecayAlt.J.IntersectionOfLocal := by
  intro E _ _ _ L hL t
  obtain ⟨hL1, -⟩ := hL
  constructor
  · intro ht P hP
    unfold Formalism.FourierDecayAlt.S6.locAt
    rw [Set.mem_setOf_eq]
    refine ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1), ?_⟩
    rw [map_one, one_mul]
    exact ht
  · intro h
    exact Jx10.inter_of_module E L hL1 t h

theorem lattice_of_local : Formalism.FourierDecayAlt.J.LatticeOfLocal := by
  intro E _ _ _ L hL Q _ pl M hcov hM
  have hint := intersection_of_local E L hL
  ext t
  rw [AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, hint]
  constructor
  · intro h p
    rw [hM]
    intro P _ hP
    exact h P hP
  · intro h P hP
    obtain ⟨p, hp⟩ := hcov P hP
    exact (hM p t).mp (h p) P hp hP

theorem pull_lattice_typed : Formalism.FourierDecayAlt.J.PullLatticeTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu t
  rw [hT E g ν s hg hpd P hP hgP K o σ hσ t]
  show (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t ∈ R ↔ _
  rw [hR, hu]
  have e : (((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) : K × K) *
      (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t =
      (σ t / (g : K), (-1) ^ s * σ (IsCMField.complexConj E t) / (g : K)) := by
    ext
    · simp [div_eq_mul_inv, mul_comm]
    · simp [div_eq_mul_inv]; ring
  rw [e]

end Formalism.FourierDecayAlt.P
