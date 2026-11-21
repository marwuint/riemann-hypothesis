import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.InhVV

open Semi Inh

variable (S : Scheme.{0}) (T : Over S)

macro "ones" : tactic => `(tactic| (repeat (first | erw [map_one] | erw [one_zpow] | erw [one_pow] | erw [inv_one] | erw [_root_.mul_one] | erw [_root_.one_mul])))

end ReciprocityTheory.ChartRestriction.G.Out.InhVV
