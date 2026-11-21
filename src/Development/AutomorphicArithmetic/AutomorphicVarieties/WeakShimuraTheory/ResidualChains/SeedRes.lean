import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChainMap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [Matrix.map_mul, Matrix.map_mul, adj_map]

private theorem isGSp_map (j : R →+* R') {ν : R} {X : M4 R} (hX : IsGSp ν X) : IsGSp (j ν) (X.map j) := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp at hX ⊢
  rw [adj_map, ← Matrix.map_mul, h, hX]

private theorem isPair_map {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (a : O →+* R) (f : R →+* R')
    (P : PD Φ.ι Γ R) (h : Φ.IsPair a P) : Φ.IsPair (f.comp a) (P.map f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hr : ∀ g, (P.map f).r g = (P.r g).map f := fun _ => rfl
  have hn : ∀ v, (P.map f).n v = (P.n v).map f := fun _ => rfl
  refine ⟨fun g => isGSp_map f (h1 g), fun g hg => ?_, ?_, fun v => ⟨?_, fun i => ?_, fun i j hij => ?_⟩,
    fun v s hs i j hij => ?_, fun v s hs i => ?_⟩
  · rw [hr, h2 g hg, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [hr]; exact h3.map (map_zero f)
  · have := isGSp_map f (h4 v).1
    rwa [map_one] at this
  · rw [hn, Matrix.map_apply, (h4 v).2.1, map_one]
  · rw [hn, Matrix.map_apply, (h4 v).2.2 i j hij, map_zero]
  · rw [hr, hn, conj_map, Matrix.map_apply, h5 v s hs i j hij, map_zero]
  · have := h6 v s hs i
    unfold PD.ψ at this ⊢
    rw [hr, hn, conj_map, Matrix.map_apply, this, map_one]

end

