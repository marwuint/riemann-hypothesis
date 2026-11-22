import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Div.CoordOpp

theorem piW_inclR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (t : E →ₐ[F] Fv F v) (e : E) :
    piW t (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = t e := by
  have h1 : compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Fv F v) e := by
    simp [compFin, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  simp only [piW, RingHom.comp_apply, h1]
  exact splitProj_inclR t e

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl F} (t : E →ₐ[F] Fv F v) (z : AE F E) :
    piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [piW, cA, compFin, splitProj]
  | add x y hx hy => simp [map_add, hx, hy]

theorem incM_map_piW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (t : E →ₐ[F] Fv F v) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (piW t) = J.map t := by
  ext i j
  simp [incM, piW_inclR]

theorem unit_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    ((mat g).map (piW t))ᵀ * J.map t * (mat g).map (piW (t.comp σ)) = J.map t := by
  have hg := g.2
  change ((mat g))ᵀ * incM F J * (mat g).map (cA σ) = incM F J at hg
  have := congrArg (fun M => M.map (piW t)) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, incM_map_piW] at this
  have e2 : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    ext i j; simp [piW_cA]
  rw [e2] at this
  simpa [Matrix.transpose_map] using this

end GlobalTheory.Div.CoordOpp

