import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

namespace ReciprocityTheory.AnForm.M

open OnePoint

noncomputable section

section Alg

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem FinHolAtlas.HoloOn.mul' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x * g x) :=
  fun j => (hf j).mul (hg j)

end Alg

namespace CompatibleChartOperations

end CompatibleChartOperations

end

end ReciprocityTheory.AnForm.M
