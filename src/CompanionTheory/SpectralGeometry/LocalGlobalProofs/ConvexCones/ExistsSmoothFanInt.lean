import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CmOrdIntId
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsIsPosDefOfBasis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFanIsPolyhedral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothProjectiveRefinementPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothPolyhedralFanRefinement

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem hasRedCover_int_proj (Y : Type) [AddCommGroup Y] [m : Module ℤ Y] [Module.Finite ℤ Y] [Module.Projective ℤ Y] :
    HasRedCover (id : ℤ → ℤ) Y := by
  obtain rfl : m = AddCommGroup.toIntModule Y := Subsingleton.elim _ _
  have : Module.Free ℤ Y := inferInstance
  exact hasRedCover_int Y

theorem dominates_int_proj (Y : Type) [AddCommGroup Y] [m : Module ℤ Y] [Module.Finite ℤ Y] [Module.Projective ℤ Y] :
    Dominates (id : ℤ → ℤ) Y := by
  obtain rfl : m = AddCommGroup.toIntModule Y := Subsingleton.elim _ _
  have : Module.Free ℤ Y := inferInstance
  exact _root_.GlobalTheory.CompanionTheory.Ar.Fan.dominates_int Y

theorem exists_smooth_fan_int : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan id g φ ∧ NoSelfInt id g φ := by
  intro g
  have hpoly : IsPolyFan (id : ℤ → ℤ) g (vorFun ℤ g) :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan ℤ id g g (fun Y _ _ _ _ => hasRedCover_int_proj Y) (by simp)
  have htw : IsTwG (0 : ℤ) (vorFun ℤ g) := fun σ _ n B => baseFun_twist _ _ _ σ n B
  obtain ⟨φ, h₁, h₂, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement ℤ id 0 cmOrd_int_id g (vorFun ℤ g)
    (fun Y _ _ _ _ => dominates_int_proj Y) hpoly htw
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.CompanionTheory.Ar.Fan
