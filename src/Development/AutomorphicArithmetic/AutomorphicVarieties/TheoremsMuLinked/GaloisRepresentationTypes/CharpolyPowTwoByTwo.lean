import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkMarks
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CsdOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeRatios

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem irr2 {G κ k A : Type} [Group G] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (r : G →* GL (Fin 2) κ) (hr : U3.MatIrr ⊤ (Pr.gm r)) (j : A →+* κ) (hj : Function.Injective j) (φ : A →+* k)
    (χ : G →* kˣ) (t : G → A) (ht : ∀ g, j (t g) = (Pr.gm r g).trace)
    (hχ : ∀ g, φ (t g) = (χ g : kˣ) + ((χ g)⁻¹ : kˣ)) (U : Subgroup G) [U.Normal] {u : G} (hu : u ∈ U)
    (hd : (Pr.gm r u).det = 1) (hne : χ u ^ 2 ≠ 1) : U3.MatIrr U (Pr.gm r) := by
  have hy : ((χ u : kˣ) : k) ^ 2 - 1 ≠ 0 := fun h => hne (Units.ext (by simpa [sub_eq_zero] using h))
  rcases Pr.cliffPrime G κ 2 Nat.prime_two r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
  · exact h
  · exfalso
    obtain ⟨a, ha⟩ := h u hu
    have e : t u ^ 2 = 4 := by
      apply hj
      rw [map_pow, ht, map_ofNat]
      rw [ha] at hd ⊢
      simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at hd ⊢
      push_cast
      linear_combination 4 * hd
    have e2 := congrArg φ e
    rw [map_pow, hχ, map_ofNat] at e2
    have e3 := (χ u).mul_inv
    apply pow_ne_zero 2 hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * e2 - (2 * ((χ u : kˣ) : k) ^ 2 + (χ u : kˣ) * ((χ u)⁻¹ : kˣ) + 1) * e3
  · exfalso
    obtain ⟨g, hg⟩ := htr 0 1
    have hne' : ∀ i, π g i ≠ i := by
      intro i hi
      fin_cases i
      · exact absurd (hg.symm.trans hi) (by decide)
      · exact absurd ((π g).injective (hg.trans hi.symm)) (by decide)
    have tr0 : ∀ s ∈ U, (Pr.gm r (g * s)).trace = 0 := fun s hs => by
      rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace κ b]
      refine Finset.sum_eq_zero fun i _ => ?_
      obtain ⟨a, ha⟩ := hπ g i
      have := hla i ⟨s, hs⟩
      simp only [Pr.gm] at this ha
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.toLin'_apply]
      simp only [Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      rw [this, Matrix.mulVec_smul, ha]
      simp [hne' i]
    have z : ∀ s ∈ U, ((χ (g * s) : kˣ) : k) ^ 2 + 1 = 0 := fun s hs => by
      have e : t (g * s) = 0 := hj (by rw [ht, tr0 s hs, map_zero])
      have e2 := hχ (g * s)
      rw [e, map_zero] at e2
      have e3 := (χ (g * s)).mul_inv
      linear_combination -((χ (g * s) : kˣ) : k) * e2 - e3
    have z1 := z 1 U.one_mem
    have z2 := z u hu
    rw [mul_one] at z1
    rw [map_mul, Units.val_mul] at z2
    apply hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * z1 - z2

private theorem pair2 {κ : Type} [Field κ] :
    ∃ J : GL (Fin 2) κ, ∀ M : Matrix (Fin 2) (Fin 2) κ, M.transpose * J.val * M = M.det • J.val := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun M => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem freeRes {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (L : Type) [Field L]
    [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : FreeAt l W) :
    FreeAt l (W.comp (Base.galEmb ℚ L Ω)) :=
  _root_.UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes L W h

