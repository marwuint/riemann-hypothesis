import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem conj_val {K M Ω : Type} [Field K] [Field M] [NumberField M] [Field Ω] [Algebra K Ω]
    [Algebra M Ω] (hM : RC M) :
    ∃ s : M → M, ∀ c : G K Ω, IsConjEl c → ∀ x : M, c (algebraMap M Ω x) = algebraMap M Ω (s x) := by
  rcases hM with hM | hM
  · refine ⟨id, fun c hc x => ?_⟩
    obtain ⟨j, hj⟩ := hc
    refine j.injective ?_
    rw [hj]
    have h : ComplexEmbedding.IsReal (j.comp (algebraMap M Ω)) := IsTotallyReal.complexEmbedding_isReal _
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 h) x
  · refine ⟨fun x => IsCMField.complexConj M x, fun c hc x => ?_⟩
    obtain ⟨j, hj⟩ := hc
    refine j.injective ?_
    rw [hj]
    exact (IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm

