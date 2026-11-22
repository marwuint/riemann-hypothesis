import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturatedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickening

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.GE

theorem geClosedProj : GEClosedProj := by
  intro R _ _ I hI N P Cs i β hi hβ
  obtain ⟨hbase, hsat, hanti, hcompat⟩ := _root_.GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family R I N Cs i β hi hβ
  obtain ⟨n₀, hlift⟩ := GlobalTheory.T.homogeneous_ideal_filtration_saturated R I N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hsat hcompat
  obtain ⟨J, hJ, h⟩ := _root_.GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal R I hI N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hanti n₀ hlift
  exact _root_.GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal R I N Cs i β hi hβ J hJ (fun e => (h e).1) (fun e => (h e).2)

end GlobalTheory.CompanionTheory.GE
