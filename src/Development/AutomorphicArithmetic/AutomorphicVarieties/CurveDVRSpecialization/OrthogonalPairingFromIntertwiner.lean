import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem norm_le_one_of_integral_padic (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l x hx

set_option linter.overlappingInstances false in
private theorem small_norm_on_maximal_ideal_power {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal A ^ n, ‖y z‖ < ε := by
  have hl0 : ((l : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : A) ≠ 0 := fun h => hl0 (by simpa using congrArg y h)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
  refine ⟨e * n, fun z hz => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  have hd : (l : A) ^ n ∣ z := by
    refine Dvd.dvd.trans ?_ hz
    rw [pow_mul, hu]
    exact pow_dvd_pow_of_dvd (Units.mul_left_dvd.2 dvd_rfl) n
  obtain ⟨w, rfl⟩ := hd
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle w)) hn

set_option linter.overlappingInstances false in
private theorem continuous_padic_embedding_rep {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {D : Type} [Group D] [TopologicalSpace D] (r : D →* GG 3 A)
    (h : UnitaryThreeInertia.AdicCont (maximalIdeal A) r) : Continuous fun g => (r g).mat.map y := by
  refine continuous_matrix fun a b => continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := small_norm_on_maximal_ideal_power y hle hε
  filter_upwards [(h n).eventually_eq g] with g' hg'
  rw [dist_eq_norm, Matrix.map_apply, Matrix.map_apply, ← map_sub]
  exact hn _ (Ideal.Quotient.eq.1 (congrFun (congrFun hg' a) b))

private theorem continuous_units_of_continuous_coe {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem orthogonal_pairing_from_intertwiner {R : Type} [CommRing R] {x y j : GG 3 R} (hj : j.mat = 1) (hj' : j.right = -1)
    (hy : y.right = 1) (h : y * j = j * x) : x.mat.transpose * Jmat R 3 * y.mat = Jmat R 3 := by
  have h1 : j.left = 1 := Units.ext hj
  have h2 := congrArg SemidirectProduct.left h
  simp only [SemidirectProduct.mul_left, h1, hj', map_one, mul_one, one_mul, sgnAct_neg_one] at h2
  rw [GG.mat, GG.mat, h2, theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R 3) (Jmat R 3),
    Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
  simp

private theorem irreducible_of_scalar_multiples {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (U : Subgroup Γ) (a : Γ → Matrix (Fin 3) (Fin 3) k)
    (h : MatIrr U a) (r : Γ' →* GL (Fin 3) k) (hr : ∀ g ∈ U, ∃ s, ∃ t : k, a g = t • (r s).val) : Af.IsIrr r := by
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hi => h W fun g hg v hv => ?_⟩
  obtain ⟨s, t, e⟩ := hr g hg
  rw [e, Matrix.smul_mulVec]
  exact W.smul_mem t (hi s v hv)

