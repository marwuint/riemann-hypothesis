import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfDiscreteOfSpanEqTopComplexPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEvaluationSpanDualFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerUnique
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_periods_eq_top_and_finrank : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  intro A _ g L u hA P hP
  obtain ⟨b, -, -⟩ := GlobalTheory.exists_basis_of_discrete_of_span_eq_top_complex_pi g u.Λ u.discrete u.full
  refine _root_.GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual (primDR A) u.Λ (2 * g) b P (fun w hw ↦ ?_) (fun p ↦ ?_)
  · have h0 : (fun l ↦ P l w) = 0 := funext hw
    have h1 := hP w
    rw [h0] at h1
    have h2 := _root_.GlobalTheory.CechPer.eq_zero_of_isPer_zero A g L u hA _ h1
    have h3 : w.1 = 0 := (_root_.GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian A hA).1 (h2.trans (map_zero _).symm)
    exact Subtype.ext h3
  · obtain ⟨x, hx⟩ := _root_.GlobalTheory.PerSurj.main A g L u hA p
    obtain ⟨c, rfl⟩ := (_root_.GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian A hA).2 x
    have hc := _root_.GlobalTheory.CechPer.mem_primDR_of_isPer A g L u hA c p hx
    exact ⟨⟨c, hc⟩, fun l ↦ congrFun (_root_.GlobalTheory.CechPer.isPer_unique A g L u _ _ _ (hP ⟨c, hc⟩) hx) l⟩

end GlobalTheory.CechPer
