import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FinSmallGen
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.MemOfForallValuationSubring
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace ChowFormHeightComparison₂.RegularPointExistence

theorem reg_of_val {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : GlobalTheory.HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev d p L ψ s) (τ : ℕ) (b : Ω)
    (hb : ∀ (la : HeightOneSpectrum (𝓞 K)) (O : ValuationSubring Ω),
      (∀ a : 𝓞 K, O.valuation (algebraMap K Ω (a : K)) ≤ 1) →
      (∀ a ∈ la.asIdeal, O.valuation (algebraMap K Ω (a : K)) < 1) →
      ∃ l ∈ W, O.valuation b ≤ O.valuation (ev l) ^ τ)
    (w : W) (hw : ev w ≠ 0) (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k) :
    GlobalTheory.Cartier.RegAt x (ψ b * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ τ) := by
  haveI := (hM.normal x).2
  refine mem_of_forall_valuationSubring fun O hO => ?_
  have hreg : ∀ g, GlobalTheory.Cartier.RegAt x g → g ∈ O := fun g ⟨a, ha⟩ => ha ▸ hO a
  obtain ⟨la, O', hle, h1, h2⟩ := exists_refine (K := K) (O.comap ψ) fun a => by
    rw [ValuationSubring.mem_comap, hM.base a]
    exact hreg _ (regAt_fnOf (TopologicalSpace.Opens.mem_top x) _ _)
  obtain ⟨l, hl, hbl⟩ := hb la O' h1 h2
  rw [← map_pow, ValuationSubring.valuation_le_iff] at hbl
  obtain ⟨c, hc⟩ := hbl
  have hcO : ψ (c : Ω) ∈ O := (ValuationSubring.mem_comap).1 (hle c.2)
  have hr := hM.ratio ⟨l, hl⟩ w k (gen_mem hx)
  have hψw : ψ (ev w) ≠ 0 := (map_ne_zero ψ).2 hw
  have e1 : ψ (ev l) * (ψ (ev w))⁻¹ * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) =
      fnOf (L.B.U k) (gen_mem hx) ((s ⟨l, hl⟩).f k) := by
    rw [mul_right_comm]
    erw [hr]
    rw [mul_right_comm, mul_inv_cancel₀ hψw, one_mul]
  have e2 : ψ b * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ τ =
      ψ (c : Ω) * fnOf (L.B.U k) (gen_mem hx) ((s ⟨l, hl⟩).f k) ^ τ := by
    rw [← e1, ← hc, map_mul, map_pow]
    ring
  rw [e2]
  exact O.mul_mem _ _ hcO (O.pow_mem (hreg _ (regAt_fnOf hx _ _)) τ)

end ChowFormHeightComparison₂.RegularPointExistence

