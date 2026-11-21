import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2RootData.OnCoroot

noncomputable section

namespace SiegelEisensteinSeries.BRoad

open Filter Topology

namespace Datum

variable {G : Type*} [Group G] [TopologicalSpace G] {r : ℕ} (D : Datum G r)

structure Plucker (L : Fin r → Type*) (ℓ : ∀ i, D.Cos → L i) (nrm : ∀ i, L i → G → ℝ) (s0 : Fin r → ℝ) : Prop where
  inj : Function.Injective (fun q : D.Cos => fun i => ℓ i q)
  pos : ∀ i l g, 0 < nrm i l g
  factor : ∀ (q : D.Cos) (g : G) (i : Fin r), D.Hv ((Quotient.out q).1 * g) i = -Real.log (nrm i (ℓ i q) g)
  zeta : ∀ i, ∀ s > s0 i, ∃ (c : ℝ) (N : ℕ), ∀ g, Summable (fun l => nrm i l g ^ (-s)) ∧
    ∑' l, nrm i l g ^ (-s) ≤ c * D.ht g ^ N
  loc : ∀ i (g0 : G), ∃ U ∈ 𝓝 g0, ∃ c > 0, ∀ g ∈ U, ∀ l, c * nrm i l g0 ≤ nrm i l g ∧ nrm i l g ≤ c⁻¹ * nrm i l g0

end Datum

end SiegelEisensteinSeries.BRoad
