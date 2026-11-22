import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel

noncomputable section

namespace GlobalTheory.Member.Inhab

section Sign

open NumberField Formalism.BasicNotions ComplexConjugate Matrix Formalism.L2.Pj Formalism.L2.Pj.DatLin
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Classical.propDecidable

theorem sqrt_im_pos (D : D7) : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [hφ]
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
  simpa using hd

end Sign

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

end GlobalTheory.Member.Inhab
