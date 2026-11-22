import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocycles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLaw
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  intro p _ k _ d G c μ hμ κ B hκ hB h1
  have hcoc : ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := _root_.GlobalTheory.Katz.isCoc_iff_mem_cocycles p k d G c μ hμ
  have hlaw := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ
  have hfun := _root_.GlobalTheory.Katz.Chart.functions_are_series p k d G c
  have hsq := (_root_.GlobalTheory.chart_square_presents p k d G c).2
  have hmap := ((_root_.GlobalTheory.Katz.isMapOf_existsUnique_and p k d d G G c c ((p : ℤ_[p]) • 𝟙 G)).2 (nmul μ p)
    (_root_.GlobalTheory.Katz.Chart.isMapOf_nmul p k d G c μ hμ p)).2
  let cz : G.cocycles := ⟨fun n => c.ev₂ n κ, (hcoc κ).1 hκ⟩
  let bB : G.funs := ⟨fun n => c.ev n B, fun n => hfun.1 n B⟩
  have key : G.cob bB = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) cz := by
    apply Subtype.ext; funext n
    change cobOne k _ (c.ev n B) = pullbackTwo (((p : ℤ_[p]) • 𝟙 G).app n) (c.ev₂ n κ)
    rw [← (hlaw.2 n B).2, hB, (hmap n).2 κ]
  obtain ⟨b', hb'⟩ := _root_.GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP G cz bB key h1
  obtain ⟨s, hs, -⟩ := hfun.2.2 b'.1 b'.2
  refine ⟨s, ?_⟩
  obtain ⟨t, -, ht⟩ := hsq (fun n => c.ev₂ n κ) (fun n => hfun.2.1 n κ)
  have e1 := ht κ (fun n => rfl)
  have e2 := ht (cob1 μ s) (fun n => by
    rw [(hlaw.2 n s).2, hs n]
    exact congrArg (fun x : G.cocycles => x.1 n) hb')
  exact e1.trans e2.symm
