import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (SymTriv Level Step FormalTorus Lv pr torus_w)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UniformizationSetting

section Triv
variable {S S' : Scheme.{0}} {G : Over S} {G' H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  [GrpObj H] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G'}

variable {S'' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_even_of_desc {Q : TQ G X} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have := Q.i_hom
  obtain ⟨s, hs, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left])
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have v' : ∀ (Z : Scheme.{0}) r (z : Z) J, Good D.M.L.L z J → val s r z J = 1 := fun Z r z J hJ =>
    (v Z r z J hJ).trans (val_one _)
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  refine TowerEx.exists_even_pull D.map (e ▸ TorusCompat.of_comp Q.i Q.q : TorusCompat _ _ Q.i 1)
    ⟨s, hs, fun T x y u z J hJ => ?_⟩ fun T x z J hJ => ?_
  · simp only [v' _ _ z J hJ, MonObj.comp_one, (isCub_cubV D.M.c hJ).face, _root_.mul_one]
  · show val s _ z J = _ * val s _ z J
    rw [v' _ _ z J hJ, v' _ _ z J hJ, MonObj.comp_one, D.M.val_sym_one hJ, _root_.mul_one]

end Triv

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    (Q' : TQ G' X) : ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i := by
  obtain ⟨Q, hQ, -⟩ := TowerEx.exists_lift hA φ hφ G G' hF (P := CP.triv G) (P' := CP.triv G')
    (IsCPMap.triv (hw := hF.1.w) (TowerEx.toBase_mul hF _)) Q' ⟨CubTriv.triv _, CubTriv.triv_even _⟩
  exact ⟨Q, hQ⟩

end GlobalTheory.UniformizationSetting
end
