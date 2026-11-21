import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right atPlace_mul_right evFin_atPlace)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul' [FiniteDimensional F E] {R : Type} [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem evFin_trace [FiniteDimensional F E] (v : Pl F) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x =>
    have e : compFin F E v (a ⊗ₜ[F] x) = evFin F v a ⊗ₜ[F] x := rfl
    rw [e, trace_tmul', trace_tmul', map_mul, AlgHom.commutes]

theorem trace_split {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = splitProj t y + splitProj (t.comp σ) y := by
  rw [← Algebra.trace_eq_of_algEquiv (splitAlgEquiv h t) y, Algebra.trace_prod_apply, splitAlgEquiv_apply]
  simp [Algebra.trace_self_apply]

theorem piW_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (y : AE F E) :
    piW (t.comp σ) (cA σ y) = piW t y := by
  have e : compFin F E v (cA σ y) = sigR (Fv F v) σ (compFin F E v y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  change splitProj (t.comp σ) (compFin F E v (cA σ y)) = splitProj t (compFin F E v y)
  rw [e]
  exact splitProj_comp_sigR h t _

theorem piW_inclR {v : Pl F} (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (AF F) x) = t x := by
  change splitProj t (evFin F v 1 ⊗ₜ[F] x) = t x
  rw [map_one]
  exact splitProj_inclR t x

end GlobalTheory.OppLinChar

namespace GlobalTheory.OppLinChar

end GlobalTheory.OppLinChar
