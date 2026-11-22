import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.HermitianDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.ComplexAt

noncomputable section

section Basic

variable {K : Type*} [Field K] [NumberField K]

def degOf {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) : ℝ :=
  arithDegree h / Module.finrank ℚ K

def deg (M : HermitianBundle K) : ℝ := degOf M.metric

def fmap (σ : K →+* ℂ) {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup E']
    [Module (𝓞 K) E'] (f : E' →ₗ[𝓞 K] E) : Fibre σ E' →ₗ[ℂ] Fibre σ E where
  toFun x := f.lTensor (ComplexAt σ) x
  map_add' := map_add _
  map_smul' := lTensor_complex_smul σ f

omit [NumberField K] in

theorem conjMap_surjective (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] :
    Function.Surjective (conjMap σ E) := by
  intro u
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul w e =>
    refine ⟨ofComplex σ (starRingEnd ℂ ((ofComplex (conjugate σ)).symm w)) ⊗ₜ e, ?_⟩
    rw [conjMap_tmul, conj_ofComplex, Complex.conj_conj]
    rfl
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end Basic

section Sub

variable {K : Type*} [Field K] [NumberField K]

end Sub

section Quotient

variable {K : Type*} [Field K] [NumberField K]

theorem isTorsionFree_quotient {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
    (hF : M.Saturated F) : Module.IsTorsionFree (𝓞 K) (M.carrier ⧸ F) := by
  refine ⟨fun a ha z w hzw ↦ ?_⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective F z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective F w
  change a • Submodule.Quotient.mk x = a • Submodule.Quotient.mk y at hzw
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← smul_sub] at hzw
  exact (Submodule.Quotient.eq F).mpr (hF a _ ha0 hzw)

variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier)

def subImage (σ : K →+* ℂ) : Submodule ℂ (FibreSpace M.metric σ) :=
  LinearMap.range ((FibreSpace.equiv M.metric σ).toLinearMap ∘ₗ fmap σ F.subtype)

def quotMap (σ : K →+* ℂ) : FibreSpace M.metric σ →ₗ[ℂ] Fibre σ (M.carrier ⧸ F) :=
  fmap σ F.mkQ ∘ₗ (FibreSpace.equiv M.metric σ).symm.toLinearMap

theorem quotMap_eq_zero_iff (σ : K →+* ℂ) (x : FibreSpace M.metric σ) :
    quotMap M F σ x = 0 ↔ x ∈ subImage M F σ := by
  have hex := Module.Flat.lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F)
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hex ((FibreSpace.equiv M.metric σ).symm x)).mp hx
    exact ⟨y, by
      change FibreSpace.equiv M.metric σ (F.subtype.lTensor (ComplexAt σ) y) = x
      rw [hy]; rfl⟩
  · rintro ⟨y, rfl⟩
    exact (hex _).mpr ⟨y, rfl⟩

theorem quotMap_surjective (σ : K →+* ℂ) : Function.Surjective (quotMap M F σ) := by
  intro ξ
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective (ComplexAt σ) (Submodule.mkQ_surjective F) ξ
  exact ⟨FibreSpace.equiv M.metric σ y, hy⟩

theorem quotMap_perp_bijective (σ : K →+* ℂ) :
    Function.Bijective (quotMap M F σ ∘ₗ (subImage M F σ)ᗮ.subtype) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h1 : (x : FibreSpace M.metric σ) ∈ subImage M F σ := (quotMap_eq_zero_iff M F σ _).mp hx
    have h2 : (x : FibreSpace M.metric σ) ∈ subImage M F σ ⊓ (subImage M F σ)ᗮ := ⟨h1, x.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  · intro ξ
    obtain ⟨y, rfl⟩ := quotMap_surjective M F σ ξ
    have hy : y ∈ subImage M F σ ⊔ (subImage M F σ)ᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; exact Submodule.mem_top
    obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    change quotMap M F σ x = quotMap M F σ (w + x)
    rw [map_add, (quotMap_eq_zero_iff M F σ w).mpr hw, zero_add]

def perpEquiv (σ : K →+* ℂ) : (subImage M F σ)ᗮ ≃ₗ[ℂ] Fibre σ (M.carrier ⧸ F) :=
  LinearEquiv.ofBijective _ (quotMap_perp_bijective M F σ)

theorem perpEquiv_apply (σ : K →+* ℂ) (x : (subImage M F σ)ᗮ) :
    perpEquiv M F σ x = quotMap M F σ x := rfl

end Quotient

section BaseChange

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [Field E] [NumberField E] [Algebra K E]

variable (K) in

abbrev resEmb (τ : E →+* ℂ) : K →+* ℂ := τ.comp (algebraMap K E)

omit [NumberField K] [NumberField E] in
theorem coe_algebraMap_integers (a : 𝓞 K) :
    ((algebraMap (𝓞 K) (𝓞 E) a : 𝓞 E) : E) = algebraMap K E (a : K) := rfl

variable (K) in

def bcScalar (τ : E →+* ℂ) (z : ComplexAt τ) : 𝓞 E →ₗ[𝓞 K] ComplexAt (resEmb K τ) where
  toFun b := ofComplex _ (τ (b : E) * (ofComplex τ).symm z)
  map_add' b b' := by
    change (τ ((b + b' : 𝓞 E) : E) * _ : ℂ) = τ (b : E) * _ + τ (b' : E) * _
    push_cast; rw [map_add, add_mul]
  map_smul' a b := by
    rw [Algebra.smul_def]
    change τ ((algebraMap (𝓞 K) (𝓞 E) a : E) * (b : E)) * _ = τ (algebraMap K E (a : K)) * (τ (b : E) * _)
    rw [coe_algebraMap_integers, map_mul, mul_assoc]

variable (M : HermitianBundle K)

def bcInner (τ : E →+* ℂ) (z : ComplexAt τ) :
    𝓞 E ⊗[𝓞 K] M.carrier →ₗ[𝓞 K] Fibre (resEmb K τ) M.carrier :=
  TensorProduct.map (bcScalar K τ z) LinearMap.id

theorem bcInner_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) (m : M.carrier) :
    bcInner M τ z (b ⊗ₜ m) = bcScalar K τ z b ⊗ₜ m := rfl

theorem bcInner_add (τ : E →+* ℂ) (z z' : ComplexAt τ) (t : 𝓞 E ⊗[𝓞 K] M.carrier) :
    bcInner M τ (z + z') t = bcInner M τ z t + bcInner M τ z' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul b m =>
    rw [bcInner_tmul, bcInner_tmul, bcInner_tmul, ← add_tmul]
    congr 1
    change (τ (b : E) * (ofComplex τ).symm (z + z') : ℂ) =
      τ (b : E) * (ofComplex τ).symm z + τ (b : E) * (ofComplex τ).symm z'
    rw [map_add, mul_add]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

def bcAdd (τ : E →+* ℂ) : ComplexAt τ →+ (𝓞 E ⊗[𝓞 K] M.carrier →+ Fibre (resEmb K τ) M.carrier) :=
  AddMonoidHom.mk' (fun z ↦ (bcInner M τ z).toAddMonoidHom)
    (fun z z' ↦ AddMonoidHom.ext fun t ↦ bcInner_add M τ z z' t)

def bcFwdAdd (τ : E →+* ℂ) :
    Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) →+ Fibre (resEmb K τ) M.carrier :=
  TensorProduct.liftAddHom (bcAdd M τ) fun e z t ↦ by
    change bcInner M τ (e • z) t = bcInner M τ z (e • t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul b m =>
      rw [smul_tmul', bcInner_tmul, bcInner_tmul]
      congr 1
      change (τ (b : E) * (ofComplex τ).symm (ofComplex τ (τ (e : E)) * z) : ℂ) =
        τ ((e : E) * (b : E)) * (ofComplex τ).symm z
      rw [map_mul, map_mul, AlgEquiv.symm_apply_apply]; ring
    | add x y hx hy => rw [map_add, hx, hy, smul_add, map_add]

theorem bcFwdAdd_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (t : 𝓞 E ⊗[𝓞 K] M.carrier) :
    bcFwdAdd M τ (z ⊗ₜ t) = bcInner M τ z t := rfl

def bcFwd (τ : E →+* ℂ) :
    Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) →ₗ[ℂ] Fibre (resEmb K τ) M.carrier where
  toFun := bcFwdAdd M τ
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z x =>
      rw [smul_tmul', bcFwdAdd_tmul, bcFwdAdd_tmul, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul b m =>
        rw [bcInner_tmul, bcInner_tmul, smul_tmul']
        congr 1
        change (τ (b : E) * (ofComplex τ).symm (ofComplex τ c * z) : ℂ) =
          c * (τ (b : E) * (ofComplex τ).symm z)
        rw [map_mul, AlgEquiv.symm_apply_apply]; ring
      | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem bcFwd_tmul_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) (m : M.carrier) :
    bcFwd M τ (z ⊗ₜ (b ⊗ₜ m)) = bcScalar K τ z b ⊗ₜ m := rfl

def bcInv (τ : E →+* ℂ) :
    Fibre (resEmb K τ) M.carrier →+ Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun w ↦ AddMonoidHom.mk'
        (fun m ↦ ((ofComplex τ ((ofComplex (resEmb K τ)).symm w)) ⊗ₜ[𝓞 E]
          ((1 : 𝓞 E) ⊗ₜ[𝓞 K] m) : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)))
        (fun m m' ↦ by simp only [tmul_add]))
      (fun w w' ↦ AddMonoidHom.ext fun m ↦ by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_tmul]))
    fun a w m ↦ by
      simp only [AddMonoidHom.mk'_apply]
      have h1 : (ofComplex τ ((ofComplex (resEmb K τ)).symm (a • w)) : ComplexAt τ) =
          (algebraMap (𝓞 K) (𝓞 E) a) • ofComplex τ ((ofComplex (resEmb K τ)).symm w) := rfl
      rw [h1, TensorProduct.smul_tmul]
      congr 1
      rw [smul_tmul', ← TensorProduct.smul_tmul, algebraMap_smul]

theorem bcInv_bcFwd (τ : E →+* ℂ) (t : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)) :
    bcInv M τ (bcFwd M τ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z x =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul b m =>
      rw [bcFwd_tmul_tmul]
      change (ofComplex τ (τ (b : E) * (ofComplex τ).symm z)) ⊗ₜ[𝓞 E] ((1 : 𝓞 E) ⊗ₜ[𝓞 K] m) = _
      have h1 : (ofComplex τ (τ (b : E) * (ofComplex τ).symm z) : ComplexAt τ) = b • z := rfl
      rw [h1, TensorProduct.smul_tmul, smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem bcFwd_injective (τ : E →+* ℂ) : Function.Injective (bcFwd M τ) := fun x y h ↦ by
  rw [← bcInv_bcFwd M τ x, ← bcInv_bcFwd M τ y, h]

theorem bcFwd_conj (τ : E →+* ℂ) (x : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)) :
    bcFwd M (conjugate τ) (conjMap τ _ x) = conjMap (resEmb K τ) M.carrier (bcFwd M τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul b m =>
      rw [conjMap_tmul, bcFwd_tmul_tmul, bcFwd_tmul_tmul, conjMap_tmul]
      congr 1
      change (starRingEnd ℂ (τ (b : E)) * starRingEnd ℂ ((ofComplex τ).symm z) : ℂ) =
        starRingEnd ℂ (τ (b : E) * (ofComplex τ).symm z)
      rw [map_mul]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

def baseChangeMetric : HermitianMetric E (𝓞 E ⊗[𝓞 K] M.carrier) where
  form τ := coreOfInjective ((FibreSpace.equiv M.metric (resEmb K τ)).toLinearMap ∘ₗ bcFwd M τ)
    (by rw [LinearMap.coe_comp]
        exact (FibreSpace.equiv M.metric (resEmb K τ)).injective.comp (bcFwd_injective M τ))
  form_conj τ x y := by
    have h := M.metric.form_conj (resEmb K τ) (bcFwd M τ x) (bcFwd M τ y)
    rw [← bcFwd_conj, ← bcFwd_conj] at h
    exact h

variable (E) in

def baseChange : HermitianBundle E := ⟨𝓞 E ⊗[𝓞 K] M.carrier, baseChangeMetric M⟩

end BaseChange

structure HermitianSpace (K : Type*) [Field K] (r : ℕ) where

  form : (K →+* ℂ) → InnerProductSpace.Core ℂ (Fin r → ℂ)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fin r → ℂ),
    (form (conjugate σ)).inner (star x) (star y) = starRingEnd ℂ ((form σ).inner x y)

section Space

variable {K : Type*} [Field K] [NumberField K]

theorem tmul_smul_field (σ : K →+* ℂ) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (z : ComplexAt σ) (c : K) (x : V) :
    z ⊗ₜ[𝓞 K] (c • x) = (ofComplex σ (σ c) * z) ⊗ₜ[𝓞 K] x := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hσd : σ (algebraMap (𝓞 K) K d) ≠ 0 := (map_ne_zero σ).mpr hd0
  set w : ComplexAt σ := ofComplex σ ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d)) with hw
  have hz : z = d • w := by
    rw [smul_def]
    change (ofComplex σ).symm z = σ (algebraMap (𝓞 K) K d) * ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d))
    field_simp
  have hx : d • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) • x) = a • x := by
    rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hd0, algebraMap_smul]
  rw [hz, TensorProduct.smul_tmul, hx, ← TensorProduct.smul_tmul]
  congr 1
  rw [smul_def, hw]
  change σ (algebraMap (𝓞 K) K a) * ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d)) =
    σ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) * (ofComplex σ).symm (d • w)
  rw [← hz, map_div₀]
  field_simp

def fieldCoordO (σ : K →+* ℂ) : Fibre σ K →ₗ[𝓞 K] ComplexAt σ :=
  TensorProduct.lift (LinearMap.mk₂ (𝓞 K) (fun z c ↦ ofComplex σ (σ c) * z)
    (fun z z' c ↦ mul_add _ _ _)
    (fun a z c ↦ by
      change ofComplex σ (σ c) * (ofComplex σ (σ (a : K)) * z) =
        ofComplex σ (σ (a : K)) * (ofComplex σ (σ c) * z)
      ring)
    (fun z c c' ↦ by rw [map_add, map_add, add_mul])
    (fun a z c ↦ by
      change ofComplex σ (σ ((a : K) * c)) * z = ofComplex σ (σ (a : K)) * (ofComplex σ (σ c) * z)
      rw [map_mul, map_mul, mul_assoc]))

def fieldCoord (σ : K →+* ℂ) : Fibre σ K →ₗ[ℂ] ℂ where
  toFun t := (ofComplex σ).symm (fieldCoordO σ t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z a =>
      rw [smul_tmul', RingHom.id_apply, smul_eq_mul]
      change (ofComplex σ).symm (ofComplex σ (σ a) * (ofComplex σ c * z)) =
        c * (ofComplex σ).symm (ofComplex σ (σ a) * z)
      simp only [map_mul, AlgEquiv.symm_apply_apply]; ring
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (r : ℕ)

def coordMap (σ : K →+* ℂ) : Fibre σ (Fin r → K) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.pi fun i ↦ fieldCoord σ ∘ₗ fmap σ (LinearMap.proj i)

variable {r}

theorem coordMap_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (v : Fin r → K) (i : Fin r) :
    coordMap r σ (z ⊗ₜ v) i = σ (v i) * (ofComplex σ).symm z := by
  change (ofComplex σ).symm (ofComplex σ (σ (v i)) * z) = _
  rw [map_mul, AlgEquiv.symm_apply_apply]

def coordInv (σ : K →+* ℂ) (w : Fin r → ℂ) : Fibre σ (Fin r → K) :=
  ∑ i, ofComplex σ (w i) ⊗ₜ[𝓞 K] (Pi.single i (1 : K) : Fin r → K)

theorem coordInv_coordMap (σ : K →+* ℂ) (t : Fibre σ (Fin r → K)) :
    coordInv σ (coordMap r σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | tmul z v =>
    simp only [coordInv, coordMap_tmul]
    have h : ∀ i, ofComplex σ (σ (v i) * (ofComplex σ).symm z) ⊗ₜ[𝓞 K]
        (Pi.single i (1 : K) : Fin r → K) = z ⊗ₜ[𝓞 K] (v i • (Pi.single i (1 : K) : Fin r → K)) := by
      intro i
      rw [tmul_smul_field, map_mul, AlgEquiv.apply_symm_apply]
    simp only [h, ← tmul_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy =>
    rw [map_add]
    simp only [coordInv, Pi.add_apply, map_add, add_tmul, Finset.sum_add_distrib] at hx hy ⊢
    rw [hx, hy]

theorem coordMap_injective (σ : K →+* ℂ) : Function.Injective (coordMap r σ) := fun s t h ↦ by
  rw [← coordInv_coordMap σ s, ← coordInv_coordMap σ t, h]

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

open IsDedekindDomain.HeightOneSpectrum in

def locVec (x : Fin r → K) : Fin r → v.adicCompletion K :=
  fun i ↦ algebraMap K (v.adicCompletion K) (x i)

def localLattice (L : Submodule (𝓞 K) (Fin r → K)) :
    Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K) :=
  Submodule.span _ (locVec v '' (L : Set (Fin r → K)))

def glMap (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    (Fin r → v.adicCompletion K) →ₗ[v.adicCompletionIntegers K] (Fin r → v.adicCompletion K) :=
  (Matrix.toLin' (g : Matrix (Fin r) (Fin r) (v.adicCompletion K))).restrictScalars _

end Space

universe u v w

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
