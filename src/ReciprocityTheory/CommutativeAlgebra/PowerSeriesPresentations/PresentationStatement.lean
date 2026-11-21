import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

namespace ReciprocityTheory.CA.PS

open IsLocalRing MvPowerSeries

universe u v

structure IsCNL (A : Type*) [CommRing A] : Prop where
  noeth : IsNoetherianRing A
  loc : IsLocalRing A
  complete : IsAdicComplete (maximalIdeal A) A

end ReciprocityTheory.CA.PS
