import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GfResZpow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.MatIrrOpenGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.WeightZeroAlgebraLeEntryAlgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrr

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

open Matrix Formalism.MainNotions.N in
private theorem ss_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) k} (h : GL (Fin n) k)
    (hh : ∀ g, ρ' g = h * ρ g * h⁻¹) (hρ : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k))
    (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (Units.mul_inv h) (Units.inv_mul h)
  have he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro g v
    rw [he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, key g v⟩)
  refine ⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [key]
    exact hW' g _ hv
  · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
    have h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))
      (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) := this
    rwa [Submodule.comap_map_eq_of_injective e.injective] at h2

private theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : Af.IsAutCsd ι r) : Af.IsAutCsd ι r' := by
  obtain ⟨π, h1, h2, h3, h4⟩ := H
  refine ⟨π, h1, h2, ss_conj h.choose h.choose_spec h3, h4.mono fun w ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]

open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H

private theorem att_iso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {k : ℕ} {ι : Qbar l ≃+* ℂ}
    {f : Af.Newform k} {r r' : G ℚ Ω →* GL (Fin 2) (Qbar l)} (h : Af.RepIso r r') (H : f.Att ι r) : f.Att ι r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨ss_conj g hg H.1, H.2.mono fun w hw A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
  · rw [hg, (hw A hA).1 s hs, mul_one, mul_inv_cancel]
  · rw [← (hw A hA).2 σ hσ, hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private def dg {R : Type} [CommRing R] (t : Rˣ) : GL (Fin 2) R where
  val := Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)]
  inv := Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp

private theorem corner_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (g : G) :
    corner (conjBy (tor R t) r g).mat =
      (dg t : Matrix (Fin 2) (Fin 2) R) * corner (r g).mat * (((dg t)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
  ext a b
  show _ = (Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)] * corner (r g).mat *
    Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)] : Matrix (Fin 2) (Fin 2) R) a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply,
    (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]
  congr 1
  · congr 1
    fin_cases a <;> simp [wt1]
  · fin_cases b <;> simp [wt1]

