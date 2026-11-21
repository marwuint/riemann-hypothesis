import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Model

variable {V : Type} [CommRing V] [IsDomain V]

theorem isMonomialTau_of_tauIn {Q : Data V} {τ₀ : Gens Q} {N : ℕ} {s : Fin N → V}
    {ε : Fin N → LinearMap.BilinForm ℤ Q.X} (h : TauIn Q τ₀ s ε) : Q.IsMonomialTau s ε := by
  intro a b
  obtain ⟨hg, k, hk, hv⟩ := h a b
  exact ⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩

end GlobalTheory.Poinc.Sep.Model
