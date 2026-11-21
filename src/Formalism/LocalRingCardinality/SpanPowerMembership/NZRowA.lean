import Formalism.LocalRingCardinality.DataRows
import Formalism.LocalRingCardinality.DataForms

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

abbrev stdH : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))

theorem stdH_frames (v : InfinitePlace K) : IsUnit ((stdH K n).X v).det := by
  rw [show (stdH K n).X v = 1 from rfl, Matrix.det_one]
  exact isUnit_one

end Std

section JB0

variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

def jB : (Fin n → K) →ₛₗ[σ] V where
  toFun x := ∑ i, σ (x i) • b i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

theorem jB_apply (x : Fin n → K) : jB σ b x = ∑ i, σ (x i) • b i := rfl

theorem jB_single (i : Fin n) : jB σ b (Pi.basisFun K (Fin n) i) = b i := by
  rw [jB_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Pi.basisFun_apply, Pi.single_eq_of_ne hk, map_zero, zero_smul]
  · simp

theorem jB_basis0 : LinearIndependent ℂ (fun i => jB σ b (Pi.basisFun K (Fin n) i)) ∧
    Submodule.span ℂ (Set.range (fun i => jB σ b (Pi.basisFun K (Fin n) i))) = ⊤ := by
  have h : (fun i => jB σ b (Pi.basisFun K (Fin n) i)) = b := funext fun i => jB_single σ b i
  rw [h]
  exact ⟨b.orthonormal.linearIndependent, by
    have := b.toBasis.span_eq
    rwa [b.coe_toBasis] at this⟩

theorem repr_jB (x : Fin n → K) (i : Fin n) : b.repr (jB σ b x) i = σ (x i) := by
  rw [jB_apply, map_sum, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, b.repr_self]; simp
  · intro k _ hk
    rw [map_smul, b.repr_self]; simp [hk]
  · simp

theorem norm_jB (x : Fin n → K) : ‖jB σ b x‖ = Real.sqrt (∑ i, ‖σ (x i)‖ ^ 2) := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_eq]
  simp only [repr_jB]

open Classical in

def genB : Finset V := Finset.univ.image b

theorem generators_mem_range : ∀ v ∈ genB b, v ∈ Set.range (jB σ b) := fun v hv => by
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact ⟨_, jB_single σ b i⟩

end JB0

section JB

variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

theorem jB_basis : LinearIndependent ℂ (fun i => jB σ b ((stdH K n).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jB σ b ((stdH K n).b i))) = ⊤ := by
  have h : (fun i => jB σ b ((stdH K n).b i)) = b := funext fun i => jB_single σ b i
  rw [h]
  exact ⟨b.orthonormal.linearIndependent, by
    have := b.toBasis.span_eq
    rwa [b.coe_toBasis] at this⟩

theorem fcoord_stdF (v : InfinitePlace K) (x : Fin n → K) (i : Fin n) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v x i =
      v.embedding (x i) := by
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt]

theorem jB_norm (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (stdH K n).b (stdH K n).X (InfinitePlace.mk σ) x = ‖jB σ b x‖ := by
  rw [norm_jB]
  show Real.sqrt (∑ i, ‖Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) (fun _ => 1) _ x i‖ ^ 2) = _
  simp only [fcoord_stdF, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

theorem genB_span : Submodule.span ℂ (genB b : Set V) = ⊤ := by
  have := b.toBasis.span_eq
  rw [b.coe_toBasis] at this
  classical
  rw [genB, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact this

def oB {O : Type} [CommRing O] (φ : O →+* ℂ) : Rows.OLat O φ V := ⟨genB b, genB_span b⟩

end JB

theorem basis_of_basis {K W M ι κ : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module ℂ M] [Fintype ι] [Fintype κ] (σ : K →+* ℂ) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent ℂ (fun i => e (b i)) ∧ Submodule.span ℂ (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent ℂ (fun i => e (b' i)) ∧ Submodule.span ℂ (Set.range fun i => e (b' i)) = ⊤ := by
  have hexp : ∀ (c : Module.Basis ι K W) (x : W), e x = ∑ i, σ (c.repr x i) • e (c i) := fun c x => by
    conv_lhs => rw [← c.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hexp' : ∀ x : W, e x = ∑ i, σ (b'.repr x i) • e (b' i) := fun x => by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hspan : Submodule.span ℂ (Set.range fun i => e (b' i)) = ⊤ := by
    rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (b i) ∈ _
    rw [hexp' (b i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨?_, hspan⟩
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis b]
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hfin : Module.finrank ℂ M = Fintype.card κ := by
    rw [Module.finrank_eq_card_basis B, hcard]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hfin.symm

end Formalism.BasicNotions.Examples₂.NZ
