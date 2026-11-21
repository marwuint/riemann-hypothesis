import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlace
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : AE F E, cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : AE F E, At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  exact @GlobalTheory.SplitSign.exists_split_sign
