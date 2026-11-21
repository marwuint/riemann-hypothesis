import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) : Fin s → Segment k := fun a =>
  Segment.ofFirst (Δ.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), c b : ℕ) : ℂ)) (Δ.isCusp_first.nu _)
    (c a) (hc a)

@[simp] theorem len_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).len = c a := rfl

theorem deg_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).deg = c a * Δ.d := rfl

end GlobalTheory.CompanionTheory.LkSegCoarse

end
