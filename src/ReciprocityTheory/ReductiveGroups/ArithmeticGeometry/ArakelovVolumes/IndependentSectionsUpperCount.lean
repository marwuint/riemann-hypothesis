import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.FirstMinimumPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement

namespace ReciprocityTheory.ChartRestriction.G.AR

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

def mono {n : ℕ} {ι Y : Type*} (s : Fin n → ι → Y → ℂ) (α : Fin n → ℕ) (j : ι) (y : Y) : ℂ :=
  ∏ k, s k j y ^ α k

def lead {n δ : ℕ} {ι Y : Type*} (s : Fin n → ι → Y → ℂ) (w0 : ι → Y → ℂ)
    (t : Fin δ → ι → Y → ℂ) (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) : ι → Y → ℂ :=
  fun j y => ∑ α ∈ multiLt n a0, ∑ k,
    cc α k * mono s α j y * w0 j y ^ (T - ∑ q, α q) * t k j y

end

end ReciprocityTheory.ChartRestriction.G.AR
