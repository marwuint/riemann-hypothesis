import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def blockLinSubst {F : Type*} [Field F] {K K' : Type*} {ι : K → Type*} {ι' : K' → Type*} [∀ k, Fintype (ι k)]
    (e : K' ≃ K) (A : ∀ k', ι' k' → ι (e k') → F) : MRingOver F ι' →ₐ[F] MRingOver F ι :=
  aeval fun q => ∑ i, C (A q.1 q.2 i) * X ⟨e q.1, i⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
