import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

