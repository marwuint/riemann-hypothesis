import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HubFon

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

end GlobalTheory.HubFon
