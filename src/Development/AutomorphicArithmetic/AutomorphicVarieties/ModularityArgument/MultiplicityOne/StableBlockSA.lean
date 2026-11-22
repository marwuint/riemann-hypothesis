import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.NoDataOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableGA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableSA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.AbsCoreA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeak
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem stableBlockSA : StableBlockSA :=
  stableSA (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues Asm.places) Asm.places
    (stableGA Pi.piFin_holds Pi.piAdm_pf Pi.growthPiJ_holds (UpperTheory.Zero.ConvolutionTheory.EB.cmbPiA piTermA Pi.twTrSum_pf) cuspReadI)

theorem mult (hW : GalWeak 4) : Mult := mult_of hW (compOf' hW) stableBlockSA

end UpperTheory.V.Z.Mult
