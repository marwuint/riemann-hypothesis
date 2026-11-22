import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLineBundlePullbackSpecLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalSymmetricLineBundleTwoTors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformisationBundleEvenClosedFibreTor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwistCP

theorem exists_cp_transl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hG U a ha
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.LocalPullGen.main R G.left M.L.L M.L.isLB a.left
  obtain ⟨P, hPL, h2, h3⟩ := _root_.GlobalTheory.TranslCP.exists_transl (Sp R) G M a ha ρ hρ
  refine ⟨P, ?_, _root_.GlobalTheory.Mum.TransEven.evenOn_translate R hR D A G hG U a ha P hPL h2 h3⟩
  rw [hPL]
  exact GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _)

end GlobalTheory.MumTwistCP
