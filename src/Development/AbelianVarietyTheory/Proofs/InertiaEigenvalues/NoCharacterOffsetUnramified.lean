import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut

namespace GlobalTheory.UnrNoChi

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM' {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem chi_one_eq_one (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ)
    {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨-, e, he⟩ := hρ
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  simp only [hγ, Units.val_one, Matrix.map_one (toK D.nd i) (map_zero _) (map_one _), Matrix.one_mulVec, hu,
    LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

end GlobalTheory.UnrNoChi

