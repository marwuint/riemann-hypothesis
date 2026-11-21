import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLen
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.KsMono
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section Phi

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

set_option synthInstance.maxHeartbeats 400000 in

theorem phi_act {k : ℕ} (M : Gw D.nd w →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : ↥(GK (D.nbr i w hw).Kw))
    (x : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (actD (stdLatG (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g) x) = actD (Br.lat (D.nbr i w hw) M) g (Br.phi (D.nbr i w hw) k x) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ x
  have key : Br.vecS (D.nbr i w hw) k ((matRep (mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g)) u) = (matRep (Br.locM (D.nbr i w hw) M) g) (Br.vecS (D.nbr i w hw) k u) := by
    funext p
    show Br.toLLK (D.nbr i w hw) (((mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M
        (Br.ι (D.nbr i w hw) g)).mulVec u) p) =
      ((Br.locM (D.nbr i w hw) M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (u j))) p
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    show Br.toLLK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (M (Br.ι (D.nbr i w hw) g) p q)) = _
    rw [Br.toLLK_alg]
    rfl
  exact congrArg (fun z : Fin k → Br.LLw (D.nbr i w hw) =>
    (Submodule.Quotient.mk z : (Fin k → Br.LLw (D.nbr i w hw)) ⧸ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k)) key

end Phi

end Formalism.MainNotions.N
