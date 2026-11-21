import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FixCnt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmegaConstruction
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCyclic

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem exists_cyc {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O)
    (ha : Function.Injective al) (hc : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    ∃ v : Fin n → O, ∀ Y : Matrix (Fin n) (Fin n) O, A * Y = Y * A → Y *ᵥ v = 0 → Y = 0 :=
  _root_.UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc A al ha hc

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B :=
  _root_.UpperTheory.Reformulated.B.OmegaConstruction.red_sub m A B

theorem UpperTheory.V.Th.h0qO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (σ : G0.G₀) (al : Fin n → O), Function.Injective al → (mat y.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ m, {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y}.ncard ≤ Nat.card (ResidueField O) ^ (m * n + C) := by
  intro l _ L G0 O _ _ _ hO _ n y σ al ha hc
  obtain ⟨v, hv⟩ := exists_cyc _ al ha hc
  let Φ : Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O :=
    (LinearMap.mulRight O (mat y.ρ σ⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ σ)) - LinearMap.id
  have hΦ : ∀ Y, Φ Y = mat y.ρ σ * Y * mat y.ρ σ⁻¹ - Y := fun _ => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n Unit (fun _ => Φ)
  have hinv : mat y.ρ σ⁻¹ * mat y.ρ σ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hr : Module.finrank O (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) ≤ n := by
    let f : (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) →ₗ[O] (Fin n → O) :=
      { toFun := fun Y => Y.1 *ᵥ v
        map_add' := fun a b => by simp [add_mulVec]
        map_smul' := fun c a => by simp [smul_mulVec] }
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro Y e
      apply Subtype.ext
      refine hv Y.1 ?_ e
      have h1 : Φ Y.1 = 0 := (Submodule.mem_iInf _).mp Y.2 ()
      rw [hΦ, sub_eq_zero] at h1
      calc mat y.ρ σ * Y.1 = mat y.ρ σ * Y.1 * mat y.ρ σ⁻¹ * mat y.ρ σ := by
            rw [Matrix.mul_assoc _ _ (mat y.ρ σ), hinv, Matrix.mul_one]
        _ = _ := by rw [h1]
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  refine ⟨C, fun m => ?_⟩
  have hs : {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y} =
      {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ _ : Unit, red m (Φ Y') = 0} := by
    ext Y
    constructor
    · intro hY
      choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)
      have e : red m (Matrix.of Y') = Y := by
        ext i j
        exact hY' i j
      refine ⟨Matrix.of Y', e, fun _ => ?_⟩
      rw [hΦ, red_sub', red_mul', red_mul', e]
      exact sub_eq_zero.mpr hY
    · rintro ⟨Y', e, h⟩
      have h1 := h ()
      rw [hΦ, red_sub', red_mul', red_mul', e] at h1
      exact sub_eq_zero.mp h1
  rw [hs]
  refine (hC m).trans ?_
  obtain ⟨-, hfin, -⟩ := hO
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.add_le_add_right (Nat.mul_le_mul_left m hr) C)
