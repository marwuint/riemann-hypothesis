import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

instance isRegularRing_fin_zero : IsRegularRing (MvPolynomial (Fin 0) ℂ) :=
  IsRegularRing.of_ringEquiv (isEmptyRingEquiv ℂ (Fin 0)).symm

end

end ReciprocityTheory.AnForm.R
