import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Definitions.Degenerations.LabKerUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZM.Model

section Zero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi Out.Inh
open scoped CategoryTheory.Obj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {k : ℕ} {J : Type}

theorem corr_comm_pull {X X' Y : Scheme.{0}} (f : X ⟶ X') {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb ((trivLB X').pull f) φ ε)) (b : LB.Gen (LB.LinComb ((trivLB X').pull f) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb ((trivLB X').pull f) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr ((trivLB X').pull f) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j'
  obtain rfl : j = fun _ _ => PUnit.unit := rfl
  obtain rfl : j' = fun _ _ => PUnit.unit := rfl
  intro _ _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, ZH.RealModel.res_res, ZH.RealModel.res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (ZH.RealModel.res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (ZH.RealModel.res_res _ _ _)
  · exact (ZH.RealModel.res_res _ _ _).symm

theorem isGen_one {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : (⟨fun _ => 1⟩ : L.Gen).IsGen := by
  intro i j; rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm

theorem weil_pull_zero {X : Scheme.{0}} (f : (𝟙_ (Over S)).left ⟶ X) (n : ℤ) {T : Over S} (x y : T ⟶ 𝟙_ (Over S)) :
    Out.WeilIs (𝟙_ (Over S)) ((trivLB X).pull f) n x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩,
    ⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm_pull _ _ _ _ _ _ _ _ (ZH.RealModel.translT_id S _) (ZH.RealModel.translT_id S _) _
    (fun j => (congrArg _ (map_one _)).trans (ZH.RealModel.res_one _))

def zeroSieg (ζ : o) (s : S ⟶ Sp o) : SiegPre 0 k ζ s where
  A := 𝟙_ (Over S)
  ab := UU.isAbelianScheme_unit S
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  rig₂ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 𝟙 _
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
    fun g _ => ⟨0, toUnit_unique _ _⟩, fun a b => by
      have : unitOn (z ^ (2 * omegaStd a b)) = 1 := by simp [omegaStd, unitOn]
      rw [this]; exact weil_pull_zero _ _ _ _⟩

end Zero

end GlobalTheory.ZM.Model
end
