import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchFlip
import Development.AutomorphicArithmetic.DivisorFrames.ConjSizeHeckeCharLocalOfMemRangeEmbedding
import Development.AutomorphicArithmetic.DivisorFrames.LocalGridTensorSizeLeOneOfUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundOfHyp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem infTensAt_of_places {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) {C : ℝ} (hC : 0 ≤ C)
    (hd : DatAt ch (C / 2)) (hc : CoefAt ch (C / 2)) : InfTensAt ch C := by
  intro σ Φ β hβ x y
  set K : ℝ := C / 2 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hK
  have h1 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => ((ch.S.term A.μ0 Φ β v).coef : ℂ)) (fun v => K * placeSz ch.G v)
    (fun v _ => absLe_rat σ _ (by simpa [hK] using hc Φ β hβ v))
  have h2 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => (ch.S.term A.μ0 Φ β v).datum (ch.S.colAt A.μ0 v x) (ch.S.rowAt A.μ0 v y)) (fun v => K * placeSz ch.G v)
    (fun v _ => by simpa [hK] using hd σ Φ β hβ v x y)
  refine absLe_mono (absLe_mul h1 h2) ?_
  rw [← Finset.mul_sum, ← two_mul, ← mul_assoc]
  have : 2 * K = C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 := by rw [hK]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (sum_placeSz_le ch.G A.μ0) (by positivity)

end GlobalTheory.ArchTens

end
