import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

noncomputable section

open CategoryTheory unitInterval
open scoped Topology

namespace UpperTheory.V.KL

abbrev ZZ : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ

abbrev singC (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ := (TopCat.toSSet.obj X).chainComplex ZZ

abbrev singH (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ := (TopCat.toSSet.obj X).homology ZZ n

theorem singH_eq (X : TopCat.{0}) (n : ℕ) :
    singH X n = ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj ZZ).obj X := rfl

end UpperTheory.V.KL

end
