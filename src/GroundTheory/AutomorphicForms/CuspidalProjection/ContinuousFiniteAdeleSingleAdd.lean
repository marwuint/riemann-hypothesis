import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

open MeasureTheory Set Function Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalProjection

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} (v : HeightOneSpectrum (𝓞 K))

def evAt : 𝔸[K] →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) v).comp
    (RingHom.snd _ _)

theorem evAt_apply (x : 𝔸[K]) : evAt v x = x.2 v := rfl

end CuspidalProjection

end

end GroundTheory.Automorphic
