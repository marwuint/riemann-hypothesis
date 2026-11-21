import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

structure Base : Prop where
  (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6nat : DivisorNaturality) (a6ring : DivisorRingCompatibility) (a6supp : DivisorSupportCondition) (a6add : DivisorAdditivity)
  (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (b1 : B1) (b2 : B2) (b3 : B3) (b4 : B4) (b5 : B5) (b7 : B7)
  (c1 : C1) (c2 : C2) (c3 : C3) (c4 : C4) (c5 : C5) (d1 : D1) (d2 : D2) (d3 : D3)
  (e1 : E1) (e2 : E2) (e3 : E3) (e4 : E4) (e6 : E6)

end LateralTheory.E.E8

end
