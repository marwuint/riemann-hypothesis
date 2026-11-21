import ReciprocityTheory.Chebotarev.EulerFac

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem Smooth.mono {E : Type} [Field E] [NumberField E] {S T : Finset (Prm E)} {a : Ideal (𝓞 E)}
    (h : Smooth S a) (hST : S ⊆ T) : Smooth T a := fun q hq => hST (h q hq)

end ReciprocityTheory.Cheb
