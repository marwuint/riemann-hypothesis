import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def nmChar {g : ℕ} (K : Type) [Field K] [Algebra (ZMod g) K] (χ : (ZMod g)ˣ →* ℂˣ) : Kˣ →* ℂˣ :=
  χ.comp (Units.map (Algebra.norm (ZMod g) : K →* ZMod g))

def IsLower {g m : ℕ} (b : Gn g m) : Prop := ∀ i j : Fin m, i < j → (b : Mt g m) i j = 0

end DiscreteGroups.sglob.DzType
