import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.MvPolynomialIsHomogeneousComapWeighted

open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Fixed

variable (K G V : Type*) [CommRing K] [Group G] [AddCommGroup V] [Module K V]
  [DistribMulAction G V] [SMulCommClass G K V]

noncomputable def fixedSubmodule : Submodule K V := (Representation.ofDistribMulAction K G V).invariants

variable {K G V} in
@[simp]
theorem mem_fixedSubmodule {v : V} : v ∈ fixedSubmodule K G V ↔ ∀ g : G, g • v = v := Iff.rfl

end Fixed

section Semilinear

variable {K L G V : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction G V] [SMulDistribClass G L V]

variable (K L G) in
theorem mem_range_of_forall_smul_eq [IsGaloisGroup G K L] (x : L)
    (hx : ∀ g : G, MulSemiringAction.toRingHom G L g x = x) : x ∈ Set.range (algebraMap K L) :=
  (IsGaloisGroup.isInvariant (G := G) (A := K) (B := L)).isInvariant x hx

theorem liftBaseChange_injective_of_fixed [IsGaloisGroup G K L] {N : Type*} [AddCommGroup N]
    [Module K N] (f : N →ₗ[K] V) (hf : Function.Injective f) (h : ∀ (g : G) n, g • f n = f n) :
    Function.Injective (f.liftBaseChange L) := by
  have := IsGaloisGroup.commutes (G := G) (A := K) (B := L)
  have hF : ∀ (g : G) t, f.liftBaseChange L
      ((MulSemiringAction.toAlgHom K L g).toLinearMap.rTensor N t) = g • f.liftBaseChange L t := by
    intro g t
    induction t with
    | zero => simp
    | tmul a n => simp [smul_distrib_smul, h]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have h1 := baseChange_rationalPart (fun g : G => MulSemiringAction.toAlgHom K L g)
    (mem_range_of_forall_smul_eq K L G) (LinearMap.ker (f.liftBaseChange L)) fun g w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hF, hw, smul_zero]
  have h2 : rationalPart K (LinearMap.ker (f.liftBaseChange L)) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have hn' : f n = 0 := by simpa using hn
    exact hf (hn'.trans (map_zero f).symm)
  rw [← LinearMap.ker_eq_bot, ← h1, h2, Submodule.baseChange_bot]

variable (L G V) in

theorem span_fixedPoints_eq_top [Finite G] [FaithfulSMul G L] :
    Submodule.span L (MulAction.fixedPoints G V) = ⊤ := by
  classical
  have := Fintype.ofFinite G
  rw [eq_top_iff]
  intro v _
  by_contra hv
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hli : LinearIndependent L fun g : G => ((MulDistribMulAction.toMonoidHom L g : L →* L) :
      L → L) :=
    (linearIndependent_monoidHom L L).comp (fun g : G => MulDistribMulAction.toMonoidHom L g)
      fun g g' h => FaithfulSMul.eq_of_smul_eq_smul (α := L) fun a => DFunLike.congr_fun h a
  have h1 := Fintype.linearIndependent_iff.1 hli (fun g => φ (g • v)) (by
    funext a
    have hfix : ∑ g : G, g • a • v ∈ MulAction.fixedPoints G V := fun g' => by
      rw [Finset.smul_sum]
      simp only [smul_smul g']
      exact Fintype.sum_equiv (Equiv.mulLeft g') _ _ fun _ => rfl
    have h2 : φ (∑ g : G, g • a • v) = 0 := by
      rw [← Submodule.mem_bot L, ← hφ0]
      exact Submodule.mem_map_of_mem (Submodule.subset_span hfix)
    simpa [smul_distrib_smul, mul_comm] using h2) 1
  rw [one_smul] at h1
  exact hφ h1

theorem isBaseChange_of_range_eq_fixed [Finite G] [IsGaloisGroup G K L] {N : Type*}
    [AddCommGroup N] [Module K N] (f : N →ₗ[K] V) (hf : Function.Injective f)
    (h : ∀ v, v ∈ LinearMap.range f ↔ ∀ g : G, g • v = v) : IsBaseChange L f := by
  have := IsGaloisGroup.faithful (G := G) (A := K) (B := L)
  suffices hs : Function.Surjective (f.liftBaseChange L) from
    have hb : Function.Bijective (f.liftBaseChange L) :=
      ⟨liftBaseChange_injective_of_fixed (G := G) f hf fun g n => (h _).1 ⟨n, rfl⟩ g, hs⟩
    IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange L) hb) fun n => by simp
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_fixedPoints_eq_top L G V, Submodule.span_le]
  intro v hv
  obtain ⟨n, rfl⟩ := (h v).2 hv
  exact ⟨1 ⊗ₜ n, by simp⟩

variable [SMulCommClass G K V]

variable (K L G V) in

theorem isBaseChange_fixedSubmodule [Finite G] [IsGaloisGroup G K L] :
    IsBaseChange L (fixedSubmodule K G V).subtype :=
  isBaseChange_of_range_eq_fixed (G := G) _ Subtype.val_injective fun v => by simp

variable (K L G V) in

noncomputable def fixedEquiv [Finite G] [IsGaloisGroup G K L] :
    L ⊗[K] fixedSubmodule K G V ≃ₗ[L] V :=
  (isBaseChange_fixedSubmodule K L G V).equiv

@[simp]
theorem fixedEquiv_tmul [Finite G] [IsGaloisGroup G K L] (a : L) (v : fixedSubmodule K G V) :
    fixedEquiv K L G V (a ⊗ₜ v) = a • (v : V) :=
  (isBaseChange_fixedSubmodule K L G V).equiv_tmul a v

variable (K G) in

noncomputable def fixedPart (W : Submodule L V) : Submodule K (fixedSubmodule K G V) :=
  (W.restrictScalars K).comap (fixedSubmodule K G V).subtype

omit [MulSemiringAction G L] [SMulDistribClass G L V] in
@[simp]
theorem mem_fixedPart {W : Submodule L V} {v : fixedSubmodule K G V} :
    v ∈ fixedPart K G W ↔ (v : V) ∈ W := Iff.rfl

end Semilinear

section Algebra

variable {K L G A : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [Ring A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
  [MulSemiringAction G A] [SMulDistribClass G L A] [SMulCommClass G K A]

variable (K L G A) in

theorem isBaseChange_fixedSubalgebra [Finite G] [IsGaloisGroup G K L] :
    IsBaseChange L (FixedPoints.subalgebra K A G).val.toLinearMap :=
  isBaseChange_of_range_eq_fixed (G := G) _ Subtype.val_injective fun v =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨v, h⟩, rfl⟩⟩

variable (K L G A) in

noncomputable def fixedAlgEquiv [Finite G] [IsGaloisGroup G K L] :
    L ⊗[K] FixedPoints.subalgebra K A G ≃ₐ[L] A :=
  AlgEquiv.ofBijective (AlgHom.liftEquiv K L _ A (FixedPoints.subalgebra K A G).val) (by
    have : ⇑(AlgHom.liftEquiv K L _ A (FixedPoints.subalgebra K A G).val) =
        (isBaseChange_fixedSubalgebra K L G A).equiv := by
      funext t
      induction t with
      | zero => simp
      | tmul a v => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [this]
    exact LinearEquiv.bijective _)

@[simp]
theorem fixedAlgEquiv_tmul [Finite G] [IsGaloisGroup G K L] (l : L)
    (a : FixedPoints.subalgebra K A G) : fixedAlgEquiv K L G A (l ⊗ₜ a) = l • (a : A) := by
  simp [fixedAlgEquiv]

section Graded

variable {ι : Type*} (𝒜 : ι → Submodule L A)

variable (K G) in

def fixedGrading (i : ι) : Submodule K (FixedPoints.subalgebra K A G) :=
  ((𝒜 i).restrictScalars K).comap (FixedPoints.subalgebra K A G).val.toLinearMap

omit [MulSemiringAction G L] [SMulDistribClass G L A] in
@[simp]
theorem mem_fixedGrading {i : ι} {a : FixedPoints.subalgebra K A G} :
    a ∈ fixedGrading K G 𝒜 i ↔ (a : A) ∈ 𝒜 i := Iff.rfl

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]

omit [MulSemiringAction G L] [SMulDistribClass G L A] in
instance fixedGrading_gradedMonoid : SetLike.GradedMonoid (fixedGrading K G 𝒜) where
  one_mem := SetLike.one_mem_graded 𝒜
  mul_mem _ _ _ _ ha hb := SetLike.mul_mem_graded (A := 𝒜) ha hb

end Graded

end Algebra

end GlobalTheory.GaloisDescent
