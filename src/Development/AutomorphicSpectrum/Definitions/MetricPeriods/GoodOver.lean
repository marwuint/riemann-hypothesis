import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IntStable

namespace GlobalTheory.CompanionTheory.Ar.HS

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GroundTheory.Heights₂.Heights
open scoped ENNReal

noncomputable section

def lin {ι Y : Type*} {m : ℕ} (e : Fin m → ι → Y → ℂ) (c : Fin m → ℂ) : ι → Y → ℂ :=
  fun i y => ∑ k, c k * e k i y

section Atlas
variable {D : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas D Y ι La)

def val (F : ι → Y → ℂ) (y : Y) : ℂ := F (A.pick y) y

def ptv {N : ℕ} (ω : Fin N → ι → Y → ℂ) (y : Y) : Fin N → ℂ := fun j => val A (ω j) y

end Atlas

structure Side (D N n₂ : ℕ) (La : Type) [AddCommGroup La] (L L₂ : La) where

  Y : Type
  [top : TopologicalSpace Y]
  [t2 : T2Space Y]
  [sc : SecondCountableTopology Y]
  [ms : MeasurableSpace Y]
  [bs : BorelSpace Y]
  conn : ConnectedSpace Y

  ι : Type

  A : WeightedAtlas D Y ι La

  ω : Fin N → ι → Y → ℂ
  ω_sec : ∀ j, A.IsSec L (ω j)
  ω_gen : ∀ y, ptv A ω y ≠ 0

  b : Fin n₂ → ι → Y → ℂ
  b_sec : ∀ k, A.IsSec L₂ (b k)
  b_gen : ∀ y, ptv A b y ≠ 0

  N₂ : ℕ

  e₂ : Fin N₂ → ι → Y → ℂ
  e₂_sec : ∀ k, A.IsSec L₂ (e₂ k)
  e₂_gen : ∀ y, ptv A e₂ y ≠ 0
  pos : A.Pos (L₂ + D • L) fun _ => 0

attribute [instance] Side.top Side.t2 Side.sc Side.ms Side.bs

end

end GlobalTheory.CompanionTheory.Ar.HS
