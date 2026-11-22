import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField

namespace GlobalTheory.DualIndex

theorem relIndex_dvd_of_le_right {G : Type*} [AddCommGroup G] (H K K' : AddSubgroup G)
    (h1 : H ≤ K') (h2 : K ≤ K') : H.relIndex K ∣ H.relIndex K' := by
  rw [← AddSubgroup.relIndex_sup_left K H,
    ← AddSubgroup.relIndex_mul_relIndex H (H ⊔ K) K' le_sup_left (sup_le h1 h2)]
  exact dvd_mul_right _ _

theorem absNorm_eq_index' {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F)) :
    Ideal.absNorm I = I.toAddSubgroup.index := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem inv_relIndex_dvd {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (K : AddSubgroup F) (hK : ∀ f ∈ K, ∀ i ∈ I, i • f ∈ (1 : Submodule (𝓞 F) F)) :
    (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex K ∣ I.toAddSubgroup.index := by
  by_cases hI : I = ⊥
  · rw [← absNorm_eq_index', hI]; simp
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 haI)
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := FaithfulSMul.algebraMap_injective _ _
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha
  have hmul : Function.Injective (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a)) :=
    mul_right_injective₀ haF
  have hJ0 : Ideal.absNorm J ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff] at h
    rw [h, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact ha hJ
  have hle : (Ideal.span {a}).toAddSubgroup ≤ J.toAddSubgroup := by
    have : Ideal.span {a} ≤ J := Ideal.dvd_iff_le.1 ⟨I, by rw [hJ, mul_comm]⟩
    exact this
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex J.toAddSubgroup = I.toAddSubgroup.index := by
    have := AddSubgroup.relIndex_mul_index hle
    rw [← absNorm_eq_index', ← absNorm_eq_index', hJ, map_mul] at this
    rw [← absNorm_eq_index', hJ]
    exact mul_right_cancel₀ hJ0 this
  rw [← h1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hmul,
    ← AddSubgroup.relIndex_map_map_of_injective (f := (algebraMap (𝓞 F) F).toAddMonoidHom)
      (Ideal.span {a}).toAddSubgroup _ hinj]
  have e : AddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a))
      (1 : Submodule (𝓞 F) F).toAddSubgroup =
      AddSubgroup.map (algebraMap (𝓞 F) F).toAddMonoidHom (Ideal.span {a}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c * a, ⟨c, rfl⟩, by simp [mul_comm]⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, by simp [mul_comm]⟩
  rw [e]
  refine relIndex_dvd_of_le_right _ _ _ (AddSubgroup.map_mono hle) ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hK f hf a haI)
  refine ⟨c, ?_, by simpa [Algebra.smul_def] using hc⟩
  have : I * Ideal.span {c} ≤ I * J := by
    rw [← hJ, Ideal.mul_le]
    intro i hi s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (hK f hf i hi)
    refine Ideal.mem_span_singleton'.2 ⟨t * d, hinj ?_⟩
    simp only [map_mul, hc, hd, Algebra.smul_def]
    ring
  have h2 : J ∣ Ideal.span {c} := by
    rw [← Ideal.dvd_iff_le] at this
    exact (mul_dvd_mul_iff_left hI).1 this
  exact (Ideal.span_singleton_le_iff_mem _).1 (Ideal.dvd_iff_le.1 h2)

variable {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (B : LinearMap.BilinForm F V)

theorem dual_anti {M L : Submodule (𝓞 F) V} (h : M ≤ L) :
    B.dualSubmodule L ≤ B.dualSubmodule M := fun _ hy x hx => hy x (h hx)

theorem dual_step (M : Submodule (𝓞 F) V) (x : V) :
    (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup.relIndex
      (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup := by
  have e1 : M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup =
      (M.comap (LinearMap.toSpanSingleton (𝓞 F) V x)).toAddSubgroup.index := by
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left]
    have := AddSubgroup.index_comap M.toAddSubgroup
      (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom
    rw [show (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom.range =
      (Submodule.span (𝓞 F) {x}).toAddSubgroup from by
        ext z; simp [Submodule.mem_span_singleton]] at this
    exact this.symm
  have e2 : (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup =
      ((1 : Submodule (𝓞 F) F).toAddSubgroup.comap (B.flip x).toAddMonoidHom) ⊓
        (B.dualSubmodule M).toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, LinearMap.BilinForm.mem_dualSubmodule,
      AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    constructor
    · intro h
      exact ⟨h x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)),
        fun z hz => h z (Submodule.mem_sup_left hz)⟩
    · rintro ⟨h1, h2⟩ z hz
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_add, LinearMap.map_smul_of_tower]
      exact add_mem (h2 m hm) (Submodule.smul_mem _ c h1)
  rw [e1, e2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  refine inv_relIndex_dvd _ _ ?_
  rintro _ ⟨y, hy, rfl⟩ i hi
  have := hy (i • x) hi
  rwa [LinearMap.map_smul_of_tower] at this

theorem mem_one_iff (z : F) : z ∈ (1 : Submodule (𝓞 F) F) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨c, rfl⟩; exact c.isIntegral_coe
  · intro h; exact ⟨⟨z, h⟩, rfl⟩

end GlobalTheory.DualIndex
