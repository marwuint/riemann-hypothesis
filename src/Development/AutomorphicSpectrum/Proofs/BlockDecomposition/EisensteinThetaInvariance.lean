import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantLeviElement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMem
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsTheta

theorem thetaInv : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  intro D n V ψ χ θ μ ω hS
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := _root_.GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl D n S (fun g a hg Φ => _root_.GlobalTheory.CompanionTheory.ThetaInvLevi.theta_levi_invariant D n V ψ χ θ μ ω hS g a hg Φ)
    (fun g b hg Φ => GlobalTheory.T.theta_sum_invariant_unipotent_translate D n V ψ χ θ μ ω hS g b hg Φ)
    (fun g hg Φ => _root_.GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl D n V ψ χ θ μ ω hS g hg Φ)
  intro Φ γ hγ
  exact hle hγ Φ

end GlobalTheory.CompanionTheory.EisCellsTheta
