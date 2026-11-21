import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution

namespace GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

noncomputable section

variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_continuousAt {A : FinHolAtlas d X} {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f)
    {x : X} (hx : x ∈ W) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
      simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hx⟩).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem isClosed_of_isAnalyticSubset {A : FinHolAtlas d X} {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx => ?_)
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have : ¬ ∀ i, f i x = 0 := fun h => hx (hSW.ge ⟨hxW, h⟩).1
  push_neg at this
  obtain ⟨i, hi⟩ := this
  have hev : ∀ᶠ y in nhds x, f i y ≠ 0 := (holoOn_continuousAt (hf i) hxW).eventually_ne hi
  filter_upwards [hev, hW.mem_nhds hxW] with y hy hyW hyS
  exact hy ((hSW.le ⟨hyS, hyW⟩).2 i)

end

end GlobalTheory.LogResInt
