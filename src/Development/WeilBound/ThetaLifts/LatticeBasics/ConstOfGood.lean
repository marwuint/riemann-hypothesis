import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DeterminantProjection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem det_ne_zero_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := fun z => by
  obtain ⟨e, A, hA⟩ := h
  let q : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr e)
  have := congrArg Matrix.det (show (Aᵀ.submatrix id q * M.submatrix q q) * (A.map star).submatrix q id = Matrix.fromBlocks 1 0 0 (-1) by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; exact hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, z, mul_zero, zero_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

omit [NumberField E] in
theorem hermND_transpose {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : IsHermND σ X.Jᵀ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨fun i j => h.herm j i, fun z => det_ne_zero_of_sig (h.sig w) ?_⟩
  rw [Matrix.det_transpose] at z
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero]

omit [NumberField E] in
theorem mem_UG_of {J : Matrix (Fin n) (Fin n) E} {g : GL (Fin n) (AE F E)} :
    g ∈ UG (cA σ) (incM F J) ↔ g ∈ HR (AF F) σ Jᵀ := by
  change (g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J) ↔ (g.1.map (sigR (AF F) σ))ᵀ * (incM F J)ᵀ * g.1 = (incM F J)ᵀ
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    show (cA σ : AE F E → AE F E) = sigR (AF F) σ from funext cA_eq]

def sec {A : Type} [CommRing A] (R : Matrix (Fin n) (Fin n) A) (h : R * R = R) : A →* Matrix (Fin n) (Fin n) A where
  toFun z := 1 + (z - 1) • R
  map_one' := by simp
  map_mul' a b := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, add_assoc, ← add_smul]
    congr 2
    ring

theorem exists_sec (hc : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ Jᵀ) (hn : 1 ≤ n) :
    ∃ S : normOne (cA σ) →* UA σ J, Continuous S ∧ (∀ z, (mat (S z)).det = (z.1 : (AE F E)ˣ)) ∧
      (∀ z : normOne (cA σ), (∃ k : E, k ≠ 0 ∧ ((z.1 : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) k) → S z ∈ ratU σ J) ∧
      ∀ (z : normOne (cA σ)) (t : AF F), t • (((z.1 : (AE F E)ˣ) : AE F E) - 1) = 0 → t • (mat (S z) - 1) = 0 := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hσ := GlobalTheory.UnitaryHeckeBaseChange.sig_sig hc
  obtain ⟨u, hu⟩ := exists_aniso (σ : E →+* E) hσ Jᵀ (fun i j => hJ.1 j i) hJ.2
  have ha := inv_mul_cancel₀ hu
  have hb : (σ : E →+* E) (hsq (σ : E →+* E) Jᵀ u)⁻¹ = (hsq (σ : E →+* E) Jᵀ u)⁻¹ := by
    rw [map_inv₀, sigma_hsq (σ : E →+* E) hσ _ fun i j => hJ.1 j i]
  generalize (hsq (σ : E →+* E) Jᵀ u)⁻¹ = b at ha hb
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hR := proj_idem' _ _ _ _ ha
  have hi : ∀ a, i ((σ : E →+* E) a) = sigR (AF F) σ (i a) := fun _ => rfl
  have hA : i b * hsq (sigR (AF F) σ) (Jᵀ.map i) (fun k => i (u k)) = 1 := by
    rw [← hsq_map i (σ : E →+* E) _ hi, ← map_mul, ha, map_one]
  have h1 := proj_unitary (sigR (AF F) σ) (GlobalTheory.UnitaryHeckeBaseChange.cA_cA hc) (Jᵀ.map i)
    (fun a b => (hi _).symm.trans (congrArg i (hJ.1 b a))) _ _ hA (by rw [← hi, hb])
  have h2 := det_proj' _ _ _ _ hA
  rw [← proj_map i (σ : E →+* E) (sigR (AF F) σ) hi] at h1 h2
  generalize proj (σ : E →+* E) Jᵀ u b = R at hR h1 h2
  have hR' : R.map i * R.map i = R.map i := by rw [← Matrix.map_mul, hR]
  have cS : Continuous (sec _ hR') := continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  refine ⟨((Units.map (sec _ hR')).comp (normOne (cA σ)).subtype).codRestrict _ fun z =>
    mem_UG_of.2 (h1 z.1 (by rw [← cA_eq, mul_comm]; exact mem_normOne.1 z.2)),
    ((Continuous.units_map _ cS).comp continuous_subtype_val).subtype_mk _, fun z => h2 _,
    fun z ⟨k, k0, hk⟩ => ⟨Units.map (sec _ hR) (Units.mk0 k k0), Units.ext (Matrix.ext fun a b => ?_)⟩, fun z t ht => ?_⟩
  · change i ((1 : Matrix _ _ E) a b + (k - 1) * R a b) =
      (1 : Matrix _ _ (AE F E)) a b + (((z.1 : (AE F E)ˣ) : AE F E) - 1) * i (R a b)
    rw [hk, map_add, map_mul, map_sub, map_one, Matrix.one_apply, Matrix.one_apply, apply_ite i, map_one, map_zero]
  · change t • (1 + (((z.1 : (AE F E)ˣ) : AE F E) - 1) • R.map i - 1) = 0
    rw [add_sub_cancel_left, ← smul_assoc, ht, zero_smul]

omit [NumberField E] in
theorem conj_mem_UAt {X : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {u : UA σ X.J} (hu : u ∈ UAt σ X ev) (g : UA σ X.J) :
    g⁻¹ * u * g ∈ UAt σ X ev := fun t ht => by
  have : mat (g⁻¹ * u * g) - 1 = mat g⁻¹ * (mat u - 1) * mat g := by
    rw [mul_sub, sub_mul, mul_one]
    exact congrArg₂ (· - ·) rfl (Units.inv_mul g.1).symm
  rw [this, ← smul_mul_assoc, ← mul_smul_comm, hu t ht, mul_zero, zero_mul]

end GlobalTheory.ThK.Dbl

end
