import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AmbientDual

theorem twist_locC (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ = TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) := by
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hχ : TruncatedSeriesCountingIdentities.chi1C C g = Units.map (ψ : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (j g)) :=
    Units.ext rfl
  show (((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ g : (↥C.LL.1)ˣ) : ↥C.LL.1) * ψ (rO D.nd i r x (j g) a b) =
    ψ ((((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (j g) a b)
  rw [MonoidHom.inv_apply, hχ, map_mul, MonoidHom.inv_apply, ← map_inv]
  rfl

end GlobalTheory.AmbientDual
