import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTestModelToClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem GlobalTheory.ZH.exists_geoTest_tMap_and_centre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), Nonempty (Q.TMap t c)) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y := by
  intro hL o Ω _ _ _ hA S ρ M U₀ EE hB Q hbig hgeo
  refine ⟨fun p _ y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y₀, Fs, hn, hF⟩ := _root_.GlobalTheory.ZH.exists_fac_of_large_test o Ω S ρ M U₀ EE hB Q p y hy
    obtain ⟨t, ht⟩ := hgeo p y₀ hn Fs
    obtain ⟨c⟩ := hF t.u ht
    exact ⟨y₀, t, c, _root_.GlobalTheory.ZH.TestMap.nonempty_tMap hL o Ω S ρ M U₀ EE hB Q p y y₀ t c hbig⟩
  · haveI := hA.ft
    haveI := hA.char
    exact ((GlobalTheory.ZH.classical_points_and_local_regularity o Ω M U₀ hB.ov.normal).1 U₀ le_rfl hB.ov.ne z hz).1
