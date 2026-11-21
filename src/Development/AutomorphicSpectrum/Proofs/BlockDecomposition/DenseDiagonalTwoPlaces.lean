import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.Adele.WeakApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.DensePair

variable {F : Type} [Field F] [NumberField F]

theorem inf_proj_fin (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    (placeMapInf w).proj ((placeMapFin v).inj y) = 0 := rfl

end GlobalTheory.CompanionTheory.SaGen.DensePair
