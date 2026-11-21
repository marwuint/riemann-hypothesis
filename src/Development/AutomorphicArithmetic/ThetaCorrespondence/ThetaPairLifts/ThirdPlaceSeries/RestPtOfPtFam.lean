import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefficientExtensionDecomposition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
namespace GlobalTheory.CrysChiOne
end GlobalTheory.CrysChiOne
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open GlobalTheory.RestPtAssembly in
theorem GlobalTheory.restPt_of_ptFam_aux41_oSplit : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, RestPt i (r i) (ρ i) π := by
  intro hF D r ρ hP h41 hO i hl π hπ
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := by
    have hx := hπ
    rw [D.Z_tie]
    rw [D.Zgood_tie] at hx
    exact hx.1
  obtain ⟨hrho, hss, hblock, hdec⟩ := _root_.GlobalTheory.PointConditions.main D r ρ hP i π hZ
  obtain ⟨hshape, heps⟩ := GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation D i
  have hG2 := ((h41 i).2.2 _ (hP.good i)).2.1
  have hX := _root_.GlobalTheory.T.semisimple_decomposition_of_good_galois_local hF D i (r i) (ρ i) π (hP.good i) hG2 hg0 hg1 hdec
  exact
    { ng0 := hg0
      ng1 := hg1
      good := hP.good i
      chi1 := fun w hw C => (hX w hw C).1
      block := hblock
      chi := fun w hw C c h1 h2 => chiRat_isCrys D i w hw C c h1 h2
      g3 := UpperTheory.GalS.jointCondition_of_constituentCondition_split D i _ (hP.good i) ((_root_.UpperTheory.GalS.g3' ((h41 i).2.2 _ (hP.good i)).2.2.1).1 (Or.inl ⟨hg0, hg1⟩)) (hO i)
      cont := hP.cont i π
      rho := hrho
      ss := hss
      eps := heps
      shape := hshape }
end
end
end
