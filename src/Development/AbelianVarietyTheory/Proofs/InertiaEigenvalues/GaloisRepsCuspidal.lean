import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.GaloisFromAdm

theorem placesOver_finite (D : D7) (l : ℕ) (hl : l ≠ 0) : (placesOver D.host.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

end GlobalTheory.GaloisFromAdm

end
