import ReciprocityTheory.Chebotarev.NZIdeal

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

def Smooth {E : Type} [Field E] [NumberField E] (S : Finset (Prm E)) (a : Ideal (𝓞 E)) : Prop :=
  ∀ q : Prm E, q.asIdeal ∣ a → q ∈ S

end ReciprocityTheory.Cheb
