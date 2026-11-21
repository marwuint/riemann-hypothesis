import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MoveQkCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsSt
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_lift_pt {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
