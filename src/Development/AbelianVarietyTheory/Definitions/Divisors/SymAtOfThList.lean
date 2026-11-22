import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.Model

theorem length_eq {S : Scheme.{0}} (P : PolAV S) (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {K : Type} [Field K]
    (hK : (m : K) ≠ 0) (x : Sp K ⟶ S) {θ : SecAt P.A P.L x} {N : ℕ} {pt : Fin N → (Over.mk x ⟶ P.A)} {c : Fin N → K}
    (H : ThList P.A P.L ρ m x θ pt c) : N = (m ^ 2) ^ (2 * P.g) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  let i : K →+* AlgebraicClosure K := algebraMap _ _
  have hK' : ((m ^ 2 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast i, map_ne_zero, Nat.cast_pow]; exact pow_ne_zero _ hK
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  rw [← TorsionFieldExt.card_torsion hL P (spMap i ≫ x) hK', ← Nat.card_fin N]
  refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨u ≫ pt a, by
    rw [← MonObj.comp_pow, (H.2.1 a).1, MonObj.comp_one]⟩) ⟨fun a b h => ?_, fun p => ?_⟩)
  · exact H.1 (TorsionFieldExt.comp_injective u _ (congrArg Subtype.val h))
  · obtain ⟨a, ha⟩ := H.2.2 _ i p.1 p.2
    exact ⟨a, Subtype.ext (Over.OverMorphism.ext ha.symm)⟩

theorem polFib_self {R : Type} [CommRing R] (P : PolAV (Sp R)) : PolFib P.A P.L P.g (𝟙 _) := by
  exact ⟨P, 𝟙 _, rfl, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A))),
    (GlobalTheory.PolBaseChange.lbIso_refl P.isLB).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)⟩

end GlobalTheory.UMin.Model
