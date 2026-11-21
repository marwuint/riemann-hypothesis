import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLoci
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetFiniteFibresIsAffineFiniteInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionLineBundlePowFiniteIntStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  intro k _ X _ p D hX P hA T hT hfin
  let Z : Closeds X := ⟨T, hT⟩
  obtain ⟨hAff, hFin⟩ := _root_.GlobalTheory.HSAmp.closeds_finite_int k X p D hX Z hfin
  haveI := hAff
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  let i := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  obtain ⟨n, s, hn, hs⟩ := GlobalTheory.T.exists_nowhereZero_section_lineBundle_pow_finite_int _ hFin (P.L.B.pull i) (LB.isLB_pull hA.isLB i)
  obtain ⟨N, u, hN, hu⟩ := _root_.GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed k X p D hX P.L.B hA _ i n s hn hs
  obtain ⟨f, hf, hfu⟩ := (_root_.GlobalTheory.HSAmp.pow_sec_dict k X p P N).1 u
  refine ⟨N, hN, f, hf, ?_⟩
  rw [hfu]
  intro x hx
  apply hu
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hx

end GlobalTheory.HSAmp
