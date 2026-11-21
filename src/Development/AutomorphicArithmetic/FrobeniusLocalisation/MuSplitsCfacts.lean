import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsRationalUnitaryDeterminantMap
import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

open UpperTheory.HF

open NumberField IsDedekindDomain Formalism.HC Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory
open scoped Pointwise

private theorem exists_place {L : Type} [Field L] [NumberField L] {p : ℕ} (hs : SplitsC L p) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  unfold SplitsC at hs
  exact Set.nonempty_of_ncard_ne_zero (hs ▸ Module.finrank_pos.ne')

