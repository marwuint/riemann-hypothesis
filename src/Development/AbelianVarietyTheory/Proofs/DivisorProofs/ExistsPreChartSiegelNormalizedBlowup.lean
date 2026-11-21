import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartAtSiegelBlowupPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletion
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin

namespace GlobalTheory.AllChart

theorem preChart_all : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, PreChart F (π ≫ z) j φ BD d x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow x
  obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, hx⟩ :=
    _root_.GlobalTheory.TChart.exists_chart_at g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
  have : IsCommMonObj G₁ := hfam.1.comm
  obtain ⟨het, hsep⟩ :=
    _root_.GlobalTheory.TChartEt.isEtaleCompletion_tautChart _root_.GlobalTheory.Poinc.Sep.sepSt g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
  have h := _root_.GlobalTheory.TChartPre.preChart_of_isEtaleCompletion g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy het hsep
  rwa [hx] at h

end GlobalTheory.AllChart
