import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Defs

def intEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    𝓞 E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (Formalism.L2.Pj.embF c τ)

end GlobalTheory.CurveRootGeometry
