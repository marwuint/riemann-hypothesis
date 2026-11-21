import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing TG ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

section H0

variable {X : Scheme.{0}} {L : LB X}

theorem h0_le (j : Fin 1 → L.ι) : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun y hy => by
  simpa using Set.mem_iInter.1 hy 0

theorem chart_le_weighted_chart_single (i : L.ι) : L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) fun _ => i := fun y hy =>
  Set.mem_iInter.2 fun _ => by simpa using hy

theorem transition_factor_single_identity (y : X) (j j' : Fin 1 → L.ι) : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 X) y j j' =
    gm (𝟙 X) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) := by
  simp [trF]

def toH0 (θ : LB.Sec L) : H0 L 1 where
  f j := (X.presheaf.map (homOfLE (h0_le j)).op).hom (θ.f (j 0))
  compat j j' := fn_ext fun y hy => by
    have hm : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j' := hy
    refine ((gs_res _ y inf_le_left hm _).trans (gs_res _ y (h0_le j) hm.1 _)).trans ((gs_compat θ _ y (h0_le j hm.1)
      (h0_le j' hm.2)).trans (Eq.symm ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
      (congrArg Units.val ((gm_linComb L _ _ (𝟙 X) y j j' hm.1 hm.2).trans (transition_factor_single_identity y j j'))))
      ((gs_res _ y inf_le_right hm _).trans (gs_res _ y (h0_le j') hm.2 _))))))

def secOfH0 (σ : H0 L 1) : LB.Sec L where
  f i := (X.presheaf.map (homOfLE (chart_le_weighted_chart_single i)).op).hom (σ.f fun _ => i)
  compat i i' := fn_ext fun y hy => by
    have hm : (𝟙 X : X ⟶ X) y ∈ L.U i ⊓ L.U i' := hy
    refine ((gs_res _ y inf_le_left hm _).trans (gs_res _ y (chart_le_weighted_chart_single i) hm.1 _)).trans ((sec_trans σ _ y (chart_le_weighted_chart_single i hm.1)
      (chart_le_weighted_chart_single i' hm.2)).trans (Eq.symm ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
      (congrArg Units.val (transition_factor_single_identity y (fun _ => i) fun _ => i').symm))
      ((gs_res _ y inf_le_right hm _).trans (gs_res _ y (chart_le_weighted_chart_single i') hm.2 _))))))

end H0

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G)

end ReciprocityTheory.ChartRestriction.G.DVR
